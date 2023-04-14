use std::collections::BTreeMap;
use std::vec;

use crate::{
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target::FunctionTarget,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    graph::DomRelation,
    graph::Graph,
    stackless_bytecode::Bytecode,
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use move_binary_format::{control_flow_graph::BlockId, file_format::CodeOffset};
use move_model::exp_generator::ExpGenerator;
use move_model::{ast::TempIndex, model::FunctionEnv};

pub struct SSAConstructionProcessor {}

impl SSAConstructionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(SSAConstructionProcessor {})
    }
}

impl FunctionTargetProcessor for SSAConstructionProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
    ) -> FunctionData {
        let original_data = data.clone();
        let mut define_once_vars: Vec<TempIndex> = vec![];
        let data_with_phi = Self::insert_phi_functions(data, func_env, &mut define_once_vars);
        let data_after_renaming =
            Self::rename_variables(data_with_phi, func_env, &mut define_once_vars);
        let func_target = FunctionTarget::new(func_env, &data_after_renaming);
        println!("{}", format!("{func_target}"));

        original_data
    }

    fn name(&self) -> String {
        "ssa construction".to_string()
    }
}

impl SSAConstructionProcessor {
    // The following function implements inserting phi-functions to original bytecodes
    fn insert_phi_functions(
        data: FunctionData,
        func_env: &FunctionEnv,
        define_once_vars: &mut Vec<TempIndex>,
    ) -> FunctionData {
        let func_target = FunctionTarget::new(func_env, &data);
        let parameter_count = func_target.get_parameter_count();
        let local_count = func_target.get_local_count();
        let mut builder = FunctionDataBuilder::new(func_env, data);
        let old_code = std::mem::take(&mut builder.data.code);
        let cfg = StacklessControlFlowGraph::new_forward(&old_code);
        let graph = Self::create_graph_from_cfg(&cfg);
        let dom_frontier = graph.compute_dominance_frontier();
        let mut def_blocks = cfg.collect_defs(&old_code);
        let mut phi_insertion_records: BTreeMap<CodeOffset, Vec<TempIndex>> = BTreeMap::new();

        for v in 0..local_count {
            if !def_blocks.contains_key(&v) {
                continue;
            }
            let working_list = def_blocks.get_mut(&v).unwrap();
            if v >= parameter_count && working_list.len() == 1 {
                define_once_vars.push(v);
                continue;
            }
            let v_def = working_list.clone();
            let mut blocks_needed_to_insert_phi: Vec<BlockId> = vec![];

            while !working_list.is_empty() {
                let x = working_list.pop().unwrap();
                if !dom_frontier.contains_key(&x) {
                    continue;
                }
                let x_df = dom_frontier.get(&x).unwrap();
                for y in x_df {
                    if !blocks_needed_to_insert_phi.contains(y) {
                        blocks_needed_to_insert_phi.push(y.clone());
                        if cfg.is_dummmy(y.clone()) {
                            continue;
                        } else {
                            let lower_offset = cfg.lower_of_block(y.clone());
                            if phi_insertion_records.contains_key(&lower_offset) {
                                let insert_variables =
                                    phi_insertion_records.get_mut(&lower_offset).unwrap();
                                insert_variables.push(v as usize);
                            } else {
                                phi_insertion_records.insert(lower_offset, vec![v]);
                            }
                        }
                        if !v_def.contains(y) {
                            working_list.push(y.clone());
                        }
                    }
                }
            }
        }

        for (offset, bc) in old_code.into_iter().enumerate() {
            let co_offset = offset as CodeOffset;
            if phi_insertion_records.contains_key(&co_offset) {
                builder.emit(bc);
                let variable_vec = phi_insertion_records.get_mut(&co_offset).unwrap();
                for v in variable_vec {
                    let new_attrid = builder.new_attr();
                    builder.emit(Bytecode::Phi(new_attrid, v.clone(), vec![], v.clone()))
                }
            } else {
                builder.emit(bc);
            }
        }
        builder.data
    }

    fn rename_variables_within_block(
        builder: &mut FunctionDataBuilder,
        old_code: &mut [Bytecode],
        dom_relation: &DomRelation<BlockId>,
        reaching_def_map: &mut BTreeMap<TempIndex, (TempIndex, BlockId)>,
        cfg: &StacklessControlFlowGraph,
        block_id: &BlockId,
        define_once_vars: &Vec<TempIndex>,
    ) {
        if !cfg.is_dummmy(block_id.clone()) {
            let instr_inds = cfg.instr_indexes(block_id.clone()).unwrap();
            for offset in instr_inds {
                let bc = &mut old_code[offset as usize];
                // update the temporaries used in this bytecode
                match bc {
                    Bytecode::Assign(_, _, src, _)
                    | Bytecode::Branch(_, _, _, src)
                    | Bytecode::Abort(_, src) => {
                        if !define_once_vars.contains(src) {
                            Self::update_reaching_def(
                                &src,
                                block_id,
                                dom_relation,
                                reaching_def_map,
                            );
                            let (src_reaching_def, _) = reaching_def_map.get(&src).unwrap();
                            if src_reaching_def.clone() != usize::MAX {
                                *src = src_reaching_def.clone()
                            }
                        }
                    }
                    Bytecode::Ret(_, srcs) | Bytecode::Call(_, _, _, srcs, _) => {
                        for src in srcs {
                            if define_once_vars.contains(src) {
                                Self::update_reaching_def(
                                    &src,
                                    block_id,
                                    dom_relation,
                                    reaching_def_map,
                                );
                                let (src_reaching_def, _) = reaching_def_map.get(&src).unwrap();
                                if src_reaching_def.clone() != usize::MAX {
                                    *src = src_reaching_def.clone()
                                }
                            }
                        }
                    }
                    _ => {}
                };
                // update the temporaries defined by this bytecode
                match bc {
                    Bytecode::Phi(_, dest, _, _)
                    | Bytecode::Assign(_, dest, _, _)
                    | Bytecode::Load(_, dest, _) => {
                        if !define_once_vars.contains(dest) {
                            Self::update_reaching_def(
                                dest,
                                block_id,
                                dom_relation,
                                reaching_def_map,
                            );
                            let new_dest = builder.new_temp(builder.get_local_type(dest.clone()));
                            let dest_reaching_def = reaching_def_map.get(&dest).unwrap();
                            reaching_def_map.insert(new_dest.clone(), dest_reaching_def.clone());
                            reaching_def_map.remove(&dest);
                            reaching_def_map
                                .insert(dest.clone(), (new_dest.clone(), block_id.clone()));
                            *dest = new_dest
                        }
                    }
                    Bytecode::Call(_, dests, _, _, _) => {
                        for dest in dests {
                            if !define_once_vars.contains(dest) {
                                Self::update_reaching_def(
                                    dest,
                                    block_id,
                                    dom_relation,
                                    reaching_def_map,
                                );
                                let new_dest =
                                    builder.new_temp(builder.get_local_type(dest.clone()));
                                let dest_reaching_def = reaching_def_map.get(&dest).unwrap();
                                reaching_def_map
                                    .insert(new_dest.clone(), dest_reaching_def.clone());
                                reaching_def_map.remove(&dest);
                                reaching_def_map
                                    .insert(dest.clone(), (new_dest.clone(), block_id.clone()));
                                *dest = new_dest
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        for succ_block_id in cfg.successors(block_id.clone()) {
            if cfg.is_dummmy(succ_block_id.clone()) {
                continue;
            }

            let instr_inds = cfg.instr_indexes(succ_block_id.clone()).unwrap();
            for offset in instr_inds {
                let bc = &mut old_code[offset as usize];
                match bc {
                    Bytecode::Label(..) => {
                        continue;
                    }
                    Bytecode::Phi(_, _, dest, original_reg) => {
                        Self::update_reaching_def(
                            &original_reg,
                            block_id,
                            dom_relation,
                            reaching_def_map,
                        );

                        if let Some((r, _)) = reaching_def_map.get(&original_reg) {
                            if !dest.contains(r) && r.clone() != usize::MAX {
                                dest.push(r.clone());
                            }
                        }
                    }
                    _ => {
                        break;
                    }
                };
            }
        }
    }

    fn rename_variables(
        mut data: FunctionData,
        func_env: &FunctionEnv,
        define_once_vars: &Vec<TempIndex>,
    ) -> FunctionData {
        let mut old_code = std::mem::take(&mut data.code);
        let func_target = FunctionTarget::new(func_env, &data);
        let parameter_count = func_target.get_parameter_count();
        let local_count = func_target.get_local_count();
        let cfg = StacklessControlFlowGraph::new_forward(&old_code);
        let graph = Self::create_graph_from_cfg(&cfg);
        let dom_relation = DomRelation::new(&graph);
        let mut reaching_def_map: BTreeMap<TempIndex, (TempIndex, BlockId)> = BTreeMap::new();
        let mut builder = FunctionDataBuilder::new(func_env, data);

        for i in 0..parameter_count {
            reaching_def_map.insert(i, (i, cfg.entry_block()));
        }
        for i in parameter_count..local_count {
            reaching_def_map.insert(i, (usize::MAX, cfg.entry_block()));
        }
        graph.compute_dominance_frontier();
        let dom_tree_dfs_res = dom_relation.depth_first_traverse(&graph);
        for block_id in dom_tree_dfs_res {
            Self::rename_variables_within_block(
                &mut builder,
                &mut old_code,
                &dom_relation,
                &mut reaching_def_map,
                &cfg,
                &block_id,
                define_once_vars,
            );
        }
        builder.data.code = old_code;
        builder.data
    }

    fn create_graph_from_cfg(cfg: &StacklessControlFlowGraph) -> Graph<BlockId> {
        let entry: BlockId = cfg.entry_block();
        let nodes: Vec<BlockId> = cfg.blocks();
        let edges: Vec<(BlockId, BlockId)> = nodes
            .iter()
            .flat_map(|x| {
                cfg.successors(*x)
                    .iter()
                    .map(|y| (*x, *y))
                    .collect::<Vec<(BlockId, BlockId)>>()
            })
            .collect();
        let graph = Graph::new(entry, nodes, edges);
        graph
    }

    fn update_reaching_def(
        v: &TempIndex,
        curr_block_id: &BlockId,
        dom_relation: &DomRelation<BlockId>,
        reaching_def_map: &mut BTreeMap<TempIndex, (TempIndex, BlockId)>,
    ) {
        if !reaching_def_map.contains_key(&v) {
            return;
        }
        let (mut r, mut id) = reaching_def_map.get(&v).unwrap().clone();
        while (r != usize::MAX)
            && (r != v.clone())
            && !(dom_relation.is_dominated_by(curr_block_id.clone(), id))
        {
            (r, id) = reaching_def_map.get(&r).unwrap().clone();
        }
        reaching_def_map.insert(v.clone(), (r, id));
    }
}
