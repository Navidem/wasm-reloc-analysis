extern crate parity_wasm;
extern crate petgraph;
extern crate wasmparser;
extern crate byteorder;
use wasmparser::WasmDecoder;
use petgraph::graphmap::DiGraphMap;
use std::{env, io, fs, path};
use std::io::Write;
use std::collections::{HashSet, HashMap};
//use std::collections::BTreeSet;
// use std::iter::FromIterator;
// use std::io::prelude::Read;
use byteorder::{LittleEndian, ByteOrder};
use parity_wasm::elements::{Deserialize, CodeSection, RelocSection, ExportSection, NameSection, 
ModuleNameSection, FunctionNameSection, MemorySection, DataSection, RelocationEntry, CustomSection,
TypeSection, FunctionSection, DataSegment, GlobalSection, TableSection, ElementSection,
Instruction, FuncBody, ImportEntry, Internal, Module, Section, Serialize, VarUint32, VarUint7};
use parity_wasm::builder::*;

#[derive(Clone, Copy, PartialEq, Ord, Eq, PartialOrd, Hash, Debug, Default)]
struct FuncEntry {
    id: u32,
    start: usize,
    end: usize
}
impl FuncEntry {
    fn size(&self) -> usize {
        self.end - self.start + 1
    }
    fn id(&self) -> u32 {
        self.id
    }
    fn end(&self) -> usize {
        self.end
    }
    fn start(&self) -> usize {
        self.start
    }
}

#[derive(Clone, Copy, PartialEq, Ord, PartialOrd, Eq, Hash, Debug, Default)]
struct MemEntry {
    id: u32,
    offset: usize,
    size: u32
}
impl MemEntry {
    fn id(&self) -> u32 {
        self.id
    }
    fn offset(&self) -> usize {
        self.offset
    }
    fn size(&self) -> u32 {
        self.size
    }
}

#[derive(Clone, Copy, PartialEq, Ord, Eq, PartialOrd, Hash, Debug, Default)]
struct TableEntry {
    index: u32
}
impl TableEntry {
    fn index(&self) -> u32 {
        self.index
    }
}

#[derive(Clone, Copy, PartialEq, Ord, Eq, PartialOrd, Hash, Debug, Default)]
struct GlobalEntry {
    index: u32
}
impl GlobalEntry {
    fn index(&self) -> u32 {
        self.index
    }
}
#[derive(Clone, Copy, PartialEq, Ord, PartialOrd, Eq, Hash, Debug)]
enum Node {
    Func(FuncEntry),
    Mem(MemEntry),
    Global(GlobalEntry),
    Table(TableEntry)
}

pub fn run_reloc_analysis() -> Result<(), Box<std::error::Error>>{
    let args: Vec<String> = env::args().collect();
    let path = path::Path::new(&args[1]);
    let file = fs::File::open(path)?;
    let mut file = io::BufReader::new(file);
    let mut func_entry_list : Vec<FuncEntry> = Vec::new();
    let mut func_counter = 0;
    let mut data_entry_list: Vec<MemEntry> = Vec::new();
    let mut data_counter = 0;

    let mut exported_func_ids: Vec<u32> = Vec::new();
    let mut exported_mem_indexes: Vec<u32> = Vec::new();
    let mut exported_global_indexes: Vec<u32> = Vec::new();
    let mut exported_table_indexes: Vec<u32> = Vec::new();


    let mut func_table_entries: Vec<u32> = Vec::new();

    let mut code_start_addr: usize = 0;
    let mut data_start_addr: usize = 0;
    let mut data_body_met: usize = 0;

    //let mut non_lazy_roots: Vec<Node> = Vec::new();
    let mut non_lazy_roots: HashSet<Node> = HashSet::new();
    let mut lazy_roots: HashSet<Node> = HashSet::new();

    let data = fs::read(path)?;
    let mut parser = wasmparser::Parser::new(&data);
    let mut next_input = wasmparser::ParserInput::Default;
    //reading the header to get code and funcs start addr; or anything related to size!
    loop {  
        let state = parser.read_with_input(next_input);
        match *state {
            wasmparser::ParserState::EndWasm => break,
            wasmparser::ParserState::BeginWasm { .. } |
            wasmparser::ParserState::EndSection =>
                next_input = wasmparser::ParserInput::Default,
            wasmparser::ParserState::BeginSection { ref code, range, .. } => {
                println!("Found section: {:?} {:?}", code, range);
                if *code == wasmparser::SectionCode::Code {
                    code_start_addr = range.start;
                    next_input = wasmparser::ParserInput::Default;
                }
                else if *code == wasmparser::SectionCode::Data {
                    data_start_addr = range.start;
                    next_input = wasmparser::ParserInput::Default;
                }
                else if *code == wasmparser::SectionCode::Export {
                    next_input = wasmparser::ParserInput::Default;
                }
                else if *code == wasmparser::SectionCode::Table {
                    next_input = wasmparser::ParserInput::Default;
                }
                else if *code == wasmparser::SectionCode::Element {
                    next_input = wasmparser::ParserInput::Default;
                }
                else { 
                    println!("Skipping Section: {:?}", code);
                    next_input = wasmparser::ParserInput::SkipSection;
                    }

            },
            wasmparser::ParserState::BeginFunctionBody { range } /*|
            wasmparser::ParserState::FunctionBodyLocals {.. } |
            wasmparser::ParserState::CodeOperator { .. } |
            wasmparser::ParserState::EndFunctionBody { .. }*/ => {
                func_entry_list.push(
                    FuncEntry{id: func_counter, start: range.start, end: range.end}
                    );
                func_counter += 1;
                next_input = wasmparser::ParserInput::SkipFunctionBody;

            },
            wasmparser::ParserState::BeginDataSectionEntry {..} |
            wasmparser::ParserState::DataSectionEntryBodyChunk {..}|
            wasmparser::ParserState::EndDataSectionEntry{..}|
            wasmparser::ParserState::EndDataSectionEntryBody{..}|
            wasmparser::ParserState::BeginInitExpressionBody{..}|
            wasmparser::ParserState::InitExpressionOperator{..}|
            wasmparser::ParserState::EndInitExpressionBody{..}
            => {
                //println!("{:#?}", state);
                //next_input = wasmparser::ParserInput::Default;
            }, 
            wasmparser::ParserState::BeginDataSectionEntryBody (size) => {
                data_entry_list.push(
                    MemEntry{id: data_counter, offset: data_body_met, size: size}
                );
                data_counter += 1;
                data_body_met += size as usize;
            },
            wasmparser::ParserState::ExportSectionEntry { field, kind, index} => {
                //println!("{:?}\n{:#?}", String::from_utf8((*field).to_vec()).unwrap(), state);
                match kind { 
                   wasmparser::ExternalKind::Function => exported_func_ids.push(index),
                   wasmparser::ExternalKind::Memory => exported_mem_indexes.push(index),
                   wasmparser::ExternalKind::Global => exported_global_indexes.push(index),
                   wasmparser::ExternalKind::Table => exported_table_indexes.push(index),
                   _ => unreachable!()
                }
            },
            wasmparser::ParserState::TableSectionEntry (..) => {
                println!("{:#?}",state );
            }
            wasmparser::ParserState::BeginElementSectionEntry(..) |
            wasmparser::ParserState::EndElementSectionEntry => {
                println!("{:#?}", state);
            }
            wasmparser::ParserState::ElementSectionEntryBody (ref elements) => {
                func_table_entries = elements.clone();
            }

            _ => {
                println!("failed on:\n{:#?}", state);
                unreachable!()
                }
        }
    }
    assert!(code_start_addr != 0);
    // println!("FUNCS: {}\n{:?}",func_counter, func_entry_list );

    let module = Module::deserialize(&mut file)?;
    let reloc_mod = module.clone().parse_reloc().unwrap();  //parses relocation section in module
    let name_reloc_mod = reloc_mod.clone().parse_names().unwrap();   // parses name section
    //println!("{:#?}", name_mod);
    let sections = name_reloc_mod.into_sections();

    let mut reloc_sections: Vec<RelocSection> = Vec::new();
    let mut export_sections: Vec<ExportSection> = Vec::new();
    let mut code_section = CodeSection::default();
    let mut name_section = NameSection::Unparsed{name_type: 0, name_payload: Vec::new()};
    let mut memory_section = MemorySection::with_entries([].to_vec());
    let mut data_section = DataSection::with_entries([].to_vec());
    let mut wasm_custom_section = CustomSection::default();
    //println!("reloc: {:#?}", reloc.unwrap() );
    for sec in sections {
        // let mut w: Vec<u8> = Vec::new();         Serializing is not accurate for section addr finding!
        // sec.clone().serialize(&mut w)?;
        // println!("sec len: {}", w.len());
        match sec{
            Section::Reloc(x) => reloc_sections.push(x),
            Section::Export(x) => export_sections.push(x),
            Section::Code(x) => code_section = x,
            Section::Name(x) => name_section = x,
            Section::Memory(x) => memory_section = x,
            Section::Data(x) => data_section = x,
            Section::Custom(x) => {
                if x.name() == "_lazy_wasm_" {
                    wasm_custom_section = x
                }
            }
            _ => (),
        };
        
    }

    if wasm_custom_section.name() != "_lazy_wasm_" {
        panic!("ERROR! no WASM_CUSTOM_SECTION");
    }

    // println!("name Section{:#?}", name_section);
    // println!("Export: {:#?}",export_sections );
    // println!("Code: {:#?}", code_section);
    // println!("Data: {:#?}", data_section );
    // println!("Reloc: {:#?}",reloc_sections );

    let mut mod_name_section = ModuleNameSection::new(""); 
    let mut func_name_section = FunctionNameSection::default();
    match name_section {
        NameSection::Module(x) => mod_name_section = x,
        NameSection::Function(x) => func_name_section = x,
        _ => (),
    }

    let mut graph = DiGraphMap::new();
    let bodies = code_section.bodies();
    let func_name_map = func_name_section.names(); 
    // println!("Dumping Table sectoion's Elements: {}", func_table_entries.len());
    // for index in func_table_entries.iter() {
    //     println!("Entry {}: {:#?}", index, func_name_map.get(*index as u32).unwrap() );
    // }
    let func_id_map = inverse_name_map(func_name_map);


    //reading wasm_custom_section payload
    println!("wasm_custom {:#?}", wasm_custom_section);
    let payload = wasm_custom_section.payload();
    // println!("{:?}", payload);
    let lazy_func_num = LittleEndian::read_u32(&payload);
    let mut met = 4;
    for _ in 0..lazy_func_num {
        let lazy_name_len = LittleEndian::read_u32(&payload[met..]) as usize;
        met += 4;
        let lazy_name = String::from_utf8(payload[met..(lazy_name_len+met)].to_vec())?;
        met += lazy_name_len;
        let lazy_id = match func_id_map.get(&lazy_name) {
            None => panic!("Couldn't find lazy function name in name section: {}", lazy_name),
            Some(x) => x
        };
        lazy_roots.insert(Node::Func(func_entry_list[*lazy_id as usize]));
        println!("{}: {}",lazy_name_len, lazy_name);
    }
    println!("lazy roots: {:?}",lazy_roots );


    for entry in exported_func_ids {
        non_lazy_roots.insert(
            Node::Func(func_entry_list[entry as usize]) //SHOULD CLONE this??
        );
    }
    for entry in exported_mem_indexes {
        non_lazy_roots.insert(
            Node::Mem(data_entry_list[entry as usize])
        );
    }
    for entry in func_table_entries {   //conservatively consider any table entry as non-lazy root
        non_lazy_roots.insert(
            Node::Func(func_entry_list[entry as usize])
        );
    }
    for entry in exported_global_indexes {
        non_lazy_roots.insert(
            Node::Global(GlobalEntry{index: entry})
        );
    }
    let mut dl_export_candidates: HashSet<Node> = HashSet::new(); // keep track of export candidates from main wasm
    for lazy in lazy_roots.iter() {
        non_lazy_roots.remove(lazy);
        //dl_export_candidates.insert(*lazy); 
    }
    //println!("non_lazy root: {}\n{:#?}", non_lazy_roots.len(), non_lazy_roots);


    for (idx, func) in bodies.iter().enumerate() {
        let code = func.code();
        for insn in code.elements() {
            match insn {
                Instruction::GetGlobal(glob_idx) |
                Instruction::SetGlobal(glob_idx)  => {
                    let src = func_entry_list[idx as usize];
                    let dst = GlobalEntry{index: *glob_idx};
                    graph.add_edge(Node::Func(src), Node::Global(dst), 0);
                }
                _ => (),
            }
        }
    }

    for reloc_sec in reloc_sections {
        if reloc_sec.name() == "reloc.CODE" {
            for reloc_entry in reloc_sec.entries(){ //reloc.CODE
                match reloc_entry {
                    RelocationEntry::FunctionIndexLeb {offset, index} => {//edge: func to func
                        let id = find_func_id(&func_entry_list, code_start_addr, offset);
                        let src = func_entry_list[id as usize].clone();
                        let dst = func_entry_list[*index as usize].clone();
                        //println!("offset {} is in {}",offset,  func_name_map.get(id).unwrap());
                        graph.add_edge(Node::Func(src), Node::Func(dst), 0); 

                    },
                    RelocationEntry::MemoryAddressI32 {offset, index, addend} |
                    RelocationEntry::MemoryAddressLeb {offset, index, addend} |
                    RelocationEntry::MemoryAddressSleb {offset, index, addend} => {//edge: func to mem
                        let id = find_func_id(&func_entry_list, code_start_addr, offset);
                        // println!("offset {} is in {}\n{:#?}",offset,  id, reloc_entry);
                        let seg_id = find_seg_id(&data_entry_list, index, addend);
                        // println!("index {} is in seg {}", index, seg_id );
                        let src = func_entry_list[id as usize].clone();
                        let dst = data_entry_list[seg_id as usize].clone();
                        graph.add_edge(Node::Func(src), Node::Mem(dst), 0);

                    },
                    _ => ()
                }
            } 
        } 
        else if reloc_sec.name() == "reloc.DATA" {
            for reloc_entry in reloc_sec.entries() {
                // println!("reloc.DATA {:#?}", reloc_entry );
                match reloc_entry {
                    RelocationEntry::MemoryAddressI32 {offset, index, addend} |
                    RelocationEntry::MemoryAddressLeb {offset, index, addend} |
                    RelocationEntry::MemoryAddressSleb {offset, index, addend} => {//edge: mem to mem
                        let src_id = find_seg_id(&data_entry_list, offset, &0);
                        let dst_id = find_seg_id(&data_entry_list, index, addend);
                        if (src_id > -1) && (dst_id > -1) { //instead of assertion in function!
                            let src = data_entry_list[src_id as usize].clone();
                            let dst = data_entry_list[dst_id as usize].clone();
                            graph.add_edge(Node::Mem(src), Node::Mem(dst), 0); 
                        }
                        else {
                            println!("some edges are skipped due to out of range offset {:#?}", reloc_entry);
                        }
                    }
                    _ => () //any other reloc section to be considered?
                }
            }
        }
        else {
            panic!("UNEXPECTED relocation section: {:#?}", reloc_sec);
        } 

    }

    /// find all reachable nodes by non_lazy_roots, and build the list of nodes just reachable from lazy_roots
    let mut non_lazy_reachable: HashSet<Node> = HashSet::new();
    let mut non_lazy_nodes: Vec<Node> = non_lazy_roots.into_iter().collect();
                                        //Vec::from_iter(non_lazy_roots.into_iter());
    let mut visited: HashSet<Node> = HashSet::new();
    let mut log = String::from("");
    loop{
        let node: Node;
        match non_lazy_nodes.pop(){
            None => break,
            Some(x) => {
                // if !lazy_roots.contains(&x){
                    non_lazy_reachable.insert(x);
                // }
                node = x;
                visited.insert(x);
            }
        }
        log += &format!("-> {:?} ", node);
        for neighbor in graph.neighbors_directed(node, petgraph::Direction::Outgoing){
            // if lazy_roots.contains(&neighbor){ //should not be required
            //     continue;
            // }
            if (!visited.contains(&neighbor)) && (!lazy_roots.contains(&neighbor)) { //skip visited nodes and lazy roots
                non_lazy_nodes.push(neighbor);
            }
        }
    }

    let mut lazy_exclusive_reachable: HashSet<Node> = HashSet::new();
    let mut lazy_nodes: Vec<Node> = lazy_roots.clone().into_iter().collect();
    visited.clear();
    loop {
        let node: Node;
        match lazy_nodes.pop() {
            None => break,
            Some(x) => {
                if !non_lazy_reachable.contains(&x) {
                    lazy_exclusive_reachable.insert(x);
                }
                else { //we've reached a node that is in non_lazy_reachable
                    dl_export_candidates.insert(x);
                }
                node = x;
                visited.insert(x);
            }
        }
        for neighbor in graph.neighbors_directed(node, petgraph::Direction::Outgoing){
            if !visited.contains(&neighbor){
                lazy_nodes.push(neighbor);
            }
        }
    }

    assert!(non_lazy_reachable.is_disjoint(&lazy_exclusive_reachable));

    println!("graph: {:#?}", graph);
    println!("reachables: {}\n{:#?}", non_lazy_reachable.len(), non_lazy_reachable);
    println!("dl exports: {:?}", dl_export_candidates);
    generate_dot_file(&graph, &non_lazy_reachable, "non_lazy.dot");
    generate_dot_file(&graph, &lazy_exclusive_reachable, "lazy.dot");

    println!("lazy exclusive reachable legend:" );
    for node in lazy_exclusive_reachable.iter() {
        match node {
            Node::Func(x) => println!("Func{}: {}",x.id(), func_name_map.get(x.id()).unwrap()),
            _ => ()
        }
    }

    //////////////////
    // build_lazy_wasm(&module, &lazy_exclusive_reachable, &lazy_roots, &dl_export_candidates);
    build_wasm(&module, &lazy_exclusive_reachable, &dl_export_candidates, &func_entry_list, &data_entry_list, false);//main
    build_wasm(&module, &lazy_exclusive_reachable, &dl_export_candidates, &func_entry_list, &data_entry_list, true);//lazy
    /////////////^^^^^ doing the division!
    Ok(())
}
/*
fn build_lazy_wasm(original_module: &Module, nodes_set: &HashSet<Node>, export_nodes: &HashSet<Node>, import_nodes: &HashSet<Node>) {
    let mut new_module = ModuleBuilder::new();
    let mut type_section: TypeSection = TypeSection::default();
    // let mut function_section: Section::Function = Section::Function::new();
    let mut code_section: CodeSection = CodeSection::default();
    for sec in original_module.sections() { 
        match sec {
            Section::Type(x) => type_section = x.clone(),
            Section::Code(x) => code_section = x.clone(),
            _ => ()
        }
    }
    for node in nodes_set {
        match node {
            Node::Func(x) => {//type, code, 
                let func_type = match type_section.types()[x.id() as usize] { //TODO: FIX it! first look into functionSection then type
                    parity_wasm::elements::Type::Function(ref x) => x,
                };
                let params = func_type.params().to_vec();
                let return_type = func_type.return_type();
                let sig = signature().with_params(params).with_return_type(return_type).build_sig();
                
                let body = code_section.bodies()[x.id() as usize].clone();
                let func = function().with_signature(sig).with_body(body).build();
                new_module.push_function(func);
            }
            Node::Mem(_x) => (), //TODO
            _ => (),    //TODO global & Table
        }

    }
    for node in import_nodes { //TODO
        match node {
            Node::Func(_x) => {
                // let external = parity_wasm::elements::External::new(x);
                // imp = import().with_external(external).build();
            }
            Node::Mem(_x) => (), //TODO
            _ => (),    //TODO global & Table
        }
    }

    for node in export_nodes {
        match node {
            Node::Func(x) => {
                let exp = export().internal().func(x.id()).field("foo").build();
                new_module.push_export(exp);
            }
            Node::Mem(_) => unreachable!(),
            _ => (),    //TODO global & Table

        }
    }
    let out_mod = new_module.build();
    let wasm_bytes = parity_wasm::serialize(out_mod).unwrap();
    let wasm_path = path::Path::new("lazy.wasm");

    let mut file = match fs::File::create(&wasm_path) {
        Err(oops) => panic! ("couldn't create wasm file! {} {:?}", oops, wasm_path),
        Ok(fl) => fl,
    };

    match file.write_all(&wasm_bytes) {
        Err(oops) => panic!("cannot write into file {}", oops),
        Ok(_) => (),
    }

} */

fn build_wasm(module: &Module, lazy_nodes: &HashSet<Node>, export_candidates: &HashSet<Node>, 
                    func_list: &Vec<FuncEntry>, data_list: &Vec<MemEntry>, is_lazy: bool) {
    let mut new_module = ModuleBuilder::new();
    let type_section = module.type_section().unwrap();
    let function_section = module.function_section().unwrap();
    let mut memory_section: MemorySection = MemorySection::default();
    let mut table_section: TableSection = TableSection::default();
    let mut element_section: ElementSection = ElementSection::default();
    
    let global_section = module.global_section().unwrap();


    for sec in module.sections() {
        match sec {
            Section::Code(code_section) => {    //if func in non lazy, make a func and add
                let funcs = parse_code_section(code_section, type_section, function_section, &lazy_nodes, &func_list, is_lazy);
                for func in funcs {
                    new_module.push_function(func);
                }
            }
            Section::Data(data_section) => {
                let data_segments = parse_data_section(data_section, &lazy_nodes, &data_list, is_lazy);
                for seg in data_segments {
                    new_module = new_module.with_data_segment(seg);  
                }
            }
            Section::Memory(mem) => {
                memory_section = mem.clone();
                new_module = new_module.memory().build(); //just a dummy memory, to be replaced later by module's memory section
            } 
            Section::Global(glob_section) => {
                let global_entries = parse_global_section(&glob_section, &lazy_nodes, is_lazy);
                for glob in global_entries {
                    new_module = new_module.with_global(glob);
                }
            }
            Section::Table(tl) => {
                table_section = tl.clone();

                let mut tl_def = TableDefinition::default();
                let dummy_expr = parity_wasm::elements::InitExpr::new(vec![Instruction::Nop, Instruction::End]);
                let tl_entry = TableEntryDefinition{offset: dummy_expr, values: vec![]};
                tl_def.elements = vec![tl_entry];
                new_module.push_table(tl_def); //this adds a dummy table and element section to be replaced later
            }
            Section::Element(el) => {
                element_section = el.clone();
            }
            Section::Export(export_section) => {
                let mut export_entries = parse_export_section(export_section, &lazy_nodes, func_list, data_list, is_lazy);
                if !is_lazy {
                    export_entries.extend(push_export_candidates(export_candidates));
                }
                // else { //export lazy nodes, already is added in parse_export_section
                //     export_entries.extend(push_candidates(lazy_nodes));
                // }
                for entry in export_entries {
                    new_module.push_export(entry);
                }
            }
            Section::Import(import_section) => {
                let mut import_entries: Vec<ImportEntry> = Vec::new();
                for entry in import_section.entries() {    //add any importEntry from original module
                    import_entries.push(entry.clone());
                }
                if !is_lazy {   //add lazy_roots
                    import_entries.extend(push_import_candidates(&lazy_nodes, &global_section));
                }
                else {  // add nodes from main.wasm
                    import_entries.extend(push_import_candidates(&export_candidates, &global_section));
                }
                for imp in import_entries {
                    new_module.push_import(imp);
                }

            }
            _ => (), //TODO others
        }
    }
    let mut out_mod = new_module.build();
    //post processing sections: memory, table, element
    for sec in out_mod.sections_mut() {
        match sec {
            Section::Memory(ref mut x) => *x = memory_section.clone(),
            Section::Table(ref mut x) => *x = table_section.clone(),
            Section::Element(ref mut x) => *x = element_section.clone(),
            _ => ()
        }
    }
    let wasm_bytes = parity_wasm::serialize(out_mod).unwrap();
    let wasm_path = if is_lazy {
            path::Path::new("lazy.wasm")
            }
            else {
            path::Path::new("main.wasm")
            };

    let mut file = match fs::File::create(&wasm_path) {
        Err(oops) => panic! ("couldn't create wasm file! {} {:?}", oops, wasm_path),
        Ok(fl) => fl,
    };

    match file.write_all(&wasm_bytes) {
        Err(oops) => panic!("cannot write into file {}", oops),
        Ok(_) => (),
    }

}
fn push_import_candidates(node_set: &HashSet<Node>, global_section: &GlobalSection) -> Vec<ImportEntry> {
    let mut out_list: Vec<ImportEntry> = Vec::new();

    for node in node_set {
        let mut import_entry = parity_wasm::elements::ImportEntry::new(String::from("module_tbd"), String::from("field_tbd"), 
            parity_wasm::elements::External::Function(0));
        match node {
            Node::Func(x) => {
                *import_entry.external_mut() = parity_wasm::elements::External::Function((*x).id());

            out_list.push(import_entry.clone());

            }
            Node::Mem(_x) => { //seems here we need to do nothing! as we have just one memory[0]
                ;
                // *import_entry.external_mut() = parity_wasm::elements::External::Memory(
                //      parity_wasm::elements::MemoryType::new(0, 1) );
            }
            Node::Global(x) => {
                let global_entries = global_section.entries();
                let glob_entry = &global_entries[(*x).index() as usize];
                *import_entry.external_mut() = parity_wasm::elements::External::Global(*glob_entry.global_type());

                out_list.push(import_entry.clone());
            }
            Node::Table(_x) => { //for now we just have one table section
                ;
                // let table_entries = table_section.entries();
                // *import_entry.external_mut() = parity_wasm::elements::External::Table(
                //     parity_wasm::
                // )
            }
        }
    }
    return out_list;
}

fn parse_export_section(export_section: &ExportSection, lazy_nodes: &HashSet<Node>, func_list: &Vec<FuncEntry>, data_list: &Vec<MemEntry>, 
                        is_lazy: bool) -> Vec<parity_wasm::elements::ExportEntry> {
    let mut out_list: Vec<parity_wasm::elements::ExportEntry> = Vec::new();
    let mut node: Node = Node::Func(func_list[0]);
    for entry in export_section.entries() {
        match entry.internal() {
            parity_wasm::elements::Internal::Function(x) => node = Node::Func(func_list[*x as usize]),
            parity_wasm::elements::Internal::Memory(x) => node = Node::Mem(data_list[*x as usize]),
            parity_wasm::elements::Internal::Global(x) => node = Node::Global(GlobalEntry{index: *x}),
            parity_wasm::elements::Internal::Table(x) => node = Node::Table(TableEntry{index: *x}),
        }
        if (!is_lazy && !lazy_nodes.contains(&node)) ||
        (is_lazy && lazy_nodes.contains(&node)) {
            out_list.push(entry.clone());
        }
        else {
            let dummy_exp = parity_wasm::elements::ExportEntry::new(String::from("dummy"), parity_wasm::elements::Internal::Function(0));
            out_list.push(dummy_exp);
        }
    }
    return out_list;
}
fn push_export_candidates(candidates: &HashSet<Node>) -> Vec<parity_wasm::elements::ExportEntry> {
    let mut out_list: Vec<parity_wasm::elements::ExportEntry> = Vec::new();
    for entry in candidates {
        let mut exp_entry = parity_wasm::elements::ExportEntry::new(String::from(""), parity_wasm::elements::Internal::Function(0));
        match entry {
            Node::Func(x) => {
                *exp_entry.field_mut() = String::from("Func");
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Function((*x).id());
            }
            Node::Mem(x) => {
                *exp_entry.field_mut() = String::from("Mem");
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Memory((*x).id());   
            }
            Node::Global(x) => {
                *exp_entry.field_mut() = String::from("Global");
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Global((*x).index() );                
            }
            Node::Table(x) => {
                *exp_entry.field_mut() = String::from("Table");
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Table((*x).index());                
            }
        }
        out_list.push(exp_entry.clone());
    }
    return out_list;
}
fn parse_global_section(global_section: &GlobalSection, lazy_nodes: &HashSet<Node>, is_lazy: bool) 
                        -> Vec<parity_wasm::elements::GlobalEntry> {
    let mut out_list: Vec<parity_wasm::elements::GlobalEntry> = Vec::new();
    for (idx, glob) in global_section.entries().iter().enumerate() {
        if (!is_lazy && !lazy_nodes.contains(&Node::Global(GlobalEntry{index: idx as u32}))) || 
        (is_lazy && lazy_nodes.contains(&Node::Global(GlobalEntry{index: idx as u32}))) {
            out_list.push(glob.clone());
        }   
        else {
            let dummy_expr = parity_wasm::elements::InitExpr::new(vec![Instruction::Nop, Instruction::End]);
            let dummy_type = parity_wasm::elements::GlobalType::new(parity_wasm::elements::ValueType::I32, false);
            let dummy_glob = parity_wasm::elements::GlobalEntry::new(dummy_type, dummy_expr);
            out_list.push(dummy_glob);
        }
    }
    return out_list;
}

fn parse_data_section(data_sectoin: &DataSection, lazy_nodes: &HashSet<Node>, data_list: &Vec<MemEntry>, 
                        is_lazy: bool) -> Vec<DataSegment> {

    let mut out_list: Vec<DataSegment> = Vec::new();
    let segments = data_sectoin.entries(); 

    for (idx, seg) in segments.iter().enumerate() { // is_lazy XNOR contains
        if (!is_lazy && !lazy_nodes.contains(&Node::Mem(data_list[idx]))) || 
         (is_lazy && lazy_nodes.contains(&Node::Mem(data_list[idx]))) {
            out_list.push(seg.clone());
        }
        else { // is in lazy list: should be NOP, as the initilizer uses it
            let dummy_expr = parity_wasm::elements::InitExpr::new(vec![Instruction::Nop, Instruction::End]);
            let dummy_seg = DataSegment::new(seg.index(), dummy_expr, vec![]);
            out_list.push(dummy_seg);
        }
    }
    return out_list;
}
fn parse_code_section(code: &CodeSection, type_section: &TypeSection, function_section: &FunctionSection,
                    lazy_nodes: &HashSet<Node>, func_list: &Vec<FuncEntry>, is_lazy: bool) -> Vec<FunctionDefinition> {
    let mut out_list: Vec<FunctionDefinition> = Vec::new();
    let ttyy = type_section.types();
    let funcs = function_section.entries();
    let bodies = code.bodies();
    for (idx, func_body) in bodies.iter().enumerate() {
        if (!is_lazy && !lazy_nodes.contains(&Node::Func(func_list[idx]))) ||
         (is_lazy && lazy_nodes.contains(&Node::Func(func_list[idx]))) {  
            let func_entry = funcs[idx];
            let func_type = match ttyy[func_entry.type_ref() as usize] {
                parity_wasm::elements::Type::Function(ref x) => x,
            };
            let params = func_type.params().to_vec();
            let return_type = func_type.return_type();
            let sig = signature().with_params(params).with_return_type(return_type).build_sig();                
            let func = function().with_signature(sig).with_body(func_body.clone()).build();
            out_list.push(func);
        }
        else {  
            let empty: Vec<parity_wasm::elements::ValueType> = vec![];
            let sig = signature().with_params(empty).with_return_type(None).build_sig();   
            let unreach_insns = parity_wasm::elements::Instructions::new(
                vec![Instruction::Unreachable, Instruction::End]
            );
            let func = function().with_signature(sig)
                        .body().with_instructions(unreach_insns).build().build();
            out_list.push(func);
        }
    }
    return out_list;
}
fn find_func_id(list: &Vec<FuncEntry>, start_addr: usize, offset: &u32) -> u32 {
    let target = start_addr + *offset as usize;
    let mut id: i32 = -1;
    for func in list {
        if func.end() >= target {
            id = (*func).id() as i32;
            break;
        }
    }
    assert!(id > -1);
    id as u32
}

fn find_seg_id(list: &Vec<MemEntry>, index: &u32, addend: &i32) -> i32 {
    let target = *index as i32  + *addend ;
    let mut met: usize = 0;
    let mut id: i32 = -1;
    for seg in list {
        let seg_size = seg.size();
        met += seg_size as usize;
        if target as usize <= met {
            id  = seg.id() as i32;
            break;
        }
    }
    // println!("met: {}", met );
    // assert!(id > -1);    //TODO: for now I'm skipping the out of range offsets!
    id //as u32
}
fn generate_dot_file(graph: &petgraph::graphmap::GraphMap<Node, i32, petgraph::Directed>, nodes_hash: &HashSet<Node>,
                    fl_name: &str){
    let mut output = "digraph G {\n".to_string();
    // let mut nodes_set: BTreeSet<Node> = root_nodes.iter().cloned().collect();
    // let mut node: Node;
    for node in nodes_hash.iter() {
        let src_text: String;
        match *node {
            Node::Func(x) => src_text = format!("Func{}", x.id()),
            Node::Mem(x) => src_text = format!("Mem{}", x.id()),
            Node::Global(x) => src_text = format!("Global{}", x.index()),
            Node::Table(x) => src_text = format!("Table{}", x.index())
        }
        for to in graph.neighbors_directed(*node, petgraph::Direction::Outgoing) {
            match to {
                Node::Func(y) => output += &format!("{} -> Func{};\n", src_text, y.id()),
                Node::Mem(y) => output += &format!("{} -> Mem{};\n", src_text, y.id()),
                Node::Global(y) => output += &format!("{} -> Global{};\n", src_text, y.index()),
                Node::Table(y) => output += &format!("{} -> Table{};\n", src_text, y.index())
            }
        }
    }
    output += "}";

    // println!("{}",output );
    let dot_file = path::Path::new(fl_name);
    let mut file = match fs::File::create(&dot_file) {
        Err(oops) => panic! ("couldn't create dot file! {} {:?}", oops, dot_file),
        Ok(fl) => fl,
    };

    match file.write_all(output.as_bytes()) {
        Err(oops) => panic!("cannot write into file {}", oops),
        Ok(_) => (),
    }
}

fn inverse_name_map(name_map: &parity_wasm::elements::IndexMap<String>) -> HashMap<String, u32> {
    let len = name_map.len();
    let mut id_map = HashMap::with_capacity(len);
    for (id, name) in name_map.iter() {
        id_map.insert(name.clone(), id);
    }
    id_map
}