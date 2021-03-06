extern crate parity_wasm;
extern crate petgraph;
extern crate wasmparser;
extern crate byteorder;
use wasmparser::WasmDecoder;
use petgraph::graphmap::DiGraphMap;
use std::{env, io, fs, path, process};
use std::io::{Write, Read, Seek, SeekFrom};
use std::collections::{HashSet, HashMap};
//use std::collections::BTreeSet;
// use std::iter::FromIterator;
// use std::io::prelude::Read;
use byteorder::{LittleEndian, ByteOrder};
use parity_wasm::elements::{Deserialize, CodeSection, RelocSection, ExportSection, NameSection, 
ModuleNameSection, FunctionNameSection, MemorySection, DataSection, RelocationEntry, CustomSection,
TypeSection, FunctionSection, DataSegment, GlobalSection, TableSection, ElementSection, ImportSection,
NameMap, IndexMap,
Instruction, FuncBody, ImportEntry, Internal, Module, Section, Serialize, VarUint32, VarUint7};
use parity_wasm::builder::*;

static STACK_ADDR: i32 = 1048576;//1160736;
static PAGE_SIZE: i32 = 4096;

#[derive(Clone, Copy, PartialEq, Ord, Eq, PartialOrd, Hash, Debug, Default)]
struct FuncEntry {
    id: u32, // is in function index space (like used by call insn)
    index: i32,     // is in local module space (sequence of locally defined funcs): special -1: for imported funcs
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
    fn index(&self) -> i32 {
        self.index
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
    let mut func_id_counter = 0;
    let mut func_index_counter = 0;
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

    let module = Module::deserialize(&mut file)?;
    ///////////////////
    let reloc_mod = module.clone().parse_reloc().unwrap();  //parses relocation section in module
    let name_reloc_mod = reloc_mod.clone().parse_names().unwrap();   // parses name section
    //println!("{:#?}", name_mod);
    let sections = name_reloc_mod.into_sections();
    ///////////////////
    // let sections = module.clone().into_sections();

    let mut reloc_sections: Vec<RelocSection> = Vec::new();
    let mut export_sections: Vec<ExportSection> = Vec::new();
    let mut code_section = CodeSection::default();
    let mut name_section = NameSection::Unparsed{name_type: 0, name_payload: Vec::new()};
    let mut memory_section = MemorySection::with_entries([].to_vec());
    let mut data_section = DataSection::with_entries([].to_vec());
    let mut wasm_custom_section = CustomSection::default();
    let mut import_section = ImportSection::default();
    //println!("reloc: {:#?}", reloc.unwrap() );
    for sec in sections {
        // let mut w: Vec<u8> = Vec::new();         Serializing is not accurate for section addr finding!
        // sec.clone().serialize(&mut w)?;
        // println!("sec len: {}", w.len());
        match sec{
            Section::Import(x) => import_section = x,
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

    let mut env_funcs_set: HashSet<u32> = HashSet::new();
    //counting number of imported functions
    for imp in import_section.entries() {
        match imp.external() {
            parity_wasm::elements::External::Function(_type_index) => {
                func_entry_list.push(
                    FuncEntry{id: func_id_counter, index: -1, start: 0, end: 0}   //special case of functions (imported)
                );
                // if imp.module() == "env"{
                //     env_funcs_set.insert(func_id_counter);
                // }
                func_id_counter += 1;
            }
            _ => (),
        }
    }
    let imported_func_num = func_id_counter;    //recording the number of imported functions
    // let nnnn_str = "name";
    // let name_str: &[u8] = nnnn_str.as_bytes();
    // let NAME = wasmparser::SectionCode::Custom{name: name_str, kind: wasmparser::CustomSectionKind::Name};
    // let mut data_copy = None;
    //reading the header to get code and funcs start addr; or anything related to size!
    loop {  
        let state = parser.read_with_input(next_input);
        // println!("dbg {:?}", state );
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
                // else if *code == NAME {
                //     // println!("code.name {} code.kind {}", name, kind );
                //     data_copy = Some(Vec::new());
                //     next_input = wasmparser::ParserInput::ReadSectionRawData;
                // }                
                else { 
                    println!("Skipping Section: {:?}", code);
                    next_input = wasmparser::ParserInput::SkipSection;
                    }

            },
            wasmparser::ParserState::BeginFunctionBody { range }  => {
                // println!("{}: {:#?}", func_counter, state);
                func_entry_list.push(
                    FuncEntry{id: func_id_counter, index: func_index_counter, start: range.start, end: range.end}
                    );
                func_id_counter += 1;
                func_index_counter += 1;
                next_input = wasmparser::ParserInput::SkipFunctionBody;

            },
            
            // wasmparser::ParserState::FunctionBodyLocals {.. } |
            // wasmparser::ParserState::CodeOperator { .. } |
            // wasmparser::ParserState::EndFunctionBody { .. } => {
            //     //next_input = wasmparser::ParserInput::SkipSection;
            // }

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

            // wasmparser::ParserState::SectionRawData (ref data)=> {
            //     println!("RAW {:?}", data);
            //     data_copy.as_mut().unwrap().extend_from_slice(data);
            //     println!("data {:?}", data_copy.clone().unwrap());
            //     next_input = wasmparser::ParserInput::Default;
            // }
            // wasmparser::ParserState::NameSectionEntry(ref n) => {
            //     println!("{:?}", n);
            // }
            _ => {
                println!("failed on:\n{:#?}", state);
                unreachable!()
                }
        }
    }
    assert!(code_start_addr != 0);
    // println!("FUNCS: {}\n{:?}",func_counter, func_entry_list );


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
        // let nn = func_name_map.get(entry).unwrap();
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
        println!("Table Entry: {} = {:?}",entry, func_name_map.get(entry as u32) )
    }
    for entry in exported_global_indexes {
        non_lazy_roots.insert(
            Node::Global(GlobalEntry{index: entry})
        );
    }
    // manually insery __run__ as non_lazy_root
    let run_func_index = *func_id_map.get("__run__").unwrap();
    let dummy_func_index = *func_id_map.get("__dummy__").unwrap(); 
    let callback_func_index = *func_id_map.get("run_load_callback").unwrap();
    non_lazy_roots.insert(Node::Func(func_entry_list[run_func_index as usize]));
    //just incase if __dummy__ is there
    non_lazy_roots.remove(&Node::Func(func_entry_list[dummy_func_index as usize]));

    let mut dl_export_candidates: HashSet<Node> = HashSet::new(); // keep track of export candidates from main wasm
    for lazy in lazy_roots.iter() {
        non_lazy_roots.remove(lazy);
        //dl_export_candidates.insert(*lazy); 
    }
    //println!("non_lazy root: {}\n{:#?}", non_lazy_roots.len(), non_lazy_roots);

    let mut env_dependant_funcs: HashSet<u32> = HashSet::new();

    for (idx, func) in bodies.iter().enumerate() {
        let code = func.code();
        let func_id = idx + imported_func_num as usize;
        for insn in code.elements() {
            match insn {
                Instruction::GetGlobal(glob_idx) |
                Instruction::SetGlobal(glob_idx)  => {
                    let src = func_entry_list[func_id];
                    let dst = GlobalEntry{index: *glob_idx};
                    graph.add_edge(Node::Func(src), Node::Global(dst), 0);
                }
                Instruction::Call(x) => {
                    if env_funcs_set.contains(&x) {
                        env_dependant_funcs.insert(func_id as u32);
                    }
                }
                _ => (),
            }
        }
    }

    //inserting it here, to be later skipped in splitter
    env_dependant_funcs.insert(dummy_func_index as u32);

    for reloc_sec in reloc_sections {
        if reloc_sec.name() == "reloc.CODE" {
            // println!("{:#?}", reloc_sec);
            for reloc_entry in reloc_sec.entries(){ //reloc.CODE
            // println!("code reloc entry {:?}",reloc_entry );
                match reloc_entry {
                    RelocationEntry::FunctionIndexLeb {offset, index} => {//edge: func to func
                        let id = find_func_id(&func_entry_list, code_start_addr, offset);
                        if id == dummy_func_index {
                            continue;
                        }
                        let src = func_entry_list[id as usize].clone();
                        let correct_index = read_index(offset, code_start_addr, &path);
                        let dst = func_entry_list[correct_index as usize].clone();
                        //println!("offset {} is in {}",offset,  func_name_map.get(id).unwrap());
                        graph.add_edge(Node::Func(src), Node::Func(dst), 0); 

                    },
                    RelocationEntry::MemoryAddressI32 {offset, index, addend} |
                    RelocationEntry::MemoryAddressLeb {offset, index, addend} |
                    RelocationEntry::MemoryAddressSleb {offset, index, addend} => {//edge: func to mem
                        let id = find_func_id(&func_entry_list, code_start_addr, offset);
                        if id == dummy_func_index {
                            continue;
                        }                        
                        // println!("offset {} is in {}\n{:#?}",offset,  id, reloc_entry);
                        let correct_index = read_index(offset, code_start_addr, &path);
                        let seg_id = find_seg_id(&data_entry_list, &correct_index, addend);
                        // println!("index {} is in seg {}", index, seg_id );
                        if (seg_id > -1) { //instead of assertion in function!
                            let src = func_entry_list[id as usize].clone();
                            let dst = data_entry_list[seg_id as usize].clone();
                            graph.add_edge(Node::Func(src), Node::Mem(dst), 0);
                        }
                        else {
                            println!("some edges are skipped due to out of range offset {:#?}", reloc_entry);
                        }

                    },
                    RelocationEntry::TableIndexI32 {offset, index} |
                    RelocationEntry::TableIndexSleb {offset, index} => {
                        println!("TABLE\n{:?}", reloc_entry );
                    }
                    _ => ()
                }
            } 
        } 
        else if reloc_sec.name() == "reloc.DATA" {
            // println!("{:#?}", reloc_sec);
            for reloc_entry in reloc_sec.entries() {
                // println!("data reloc entry {:#?}", reloc_entry );
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

    // println!("graph: {:#?}", graph);
    // println!("reachables: {}\n{:#?}", non_lazy_reachable.len(), non_lazy_reachable);
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
    // let mut main_match_func_id: HashMap<u32,u32> = HashMap::new();  //a map from old func id to new

    build_wasm(&module, &lazy_exclusive_reachable, &mut dl_export_candidates, &func_entry_list, &func_name_map, &data_entry_list, &env_dependant_funcs, 
        run_func_index, callback_func_index, lazy_func_num, false);//main
    build_wasm(&module, &lazy_exclusive_reachable, &mut dl_export_candidates, &func_entry_list, &func_name_map, &data_entry_list, &env_dependant_funcs, 
        0, 0, lazy_func_num, true);//lazy
    /////////////^^^^^ doing the division!
    Ok(())
}

fn read_index(offset: &u32, code_start: usize, path: &path::Path) -> u32 {
    let index: u32;
    let mut f = fs::File::open(path).unwrap();
    //f.take((code_start+ (*offset as usize))as u64 );
    f.seek(SeekFrom::Start( (code_start + (*offset as usize))as u64 ));
    index = VarUint32::deserialize(&mut f).unwrap().into();
    return index;
}

fn build_wasm(module: &Module, lazy_nodes: &HashSet<Node>, export_candidates: &mut HashSet<Node>, 
                    func_list: &Vec<FuncEntry>, func_name_map: &NameMap, data_list: &Vec<MemEntry>, env_dependant_funcs: &HashSet<u32>,
                    old_run_id: u32, old_callback_id: u32, lazy_func_num: u32, is_lazy: bool) {
    let mod_name = module.clone().parse_names().unwrap();
    let mut new_module = ModuleBuilder::new(); //parity_wasm::builder::from_module(mod_name.clone());///
    let function_section = module.function_section().unwrap();
    let mut memory_section: MemorySection = MemorySection::default();
    let mut table_section: TableSection = TableSection::default();
    let mut element_section: ElementSection = ElementSection::default();
    let mut import_func_map: HashMap<u32, u32> = HashMap::new();
    //let mut imported_func_num: u32 = 0;
    let mut match_func_id: HashMap<u32,u32> = HashMap::new();  //a map from old func id to new


    let name_section = mod_name.names_section().unwrap();
    let mut func_name_section = FunctionNameSection::default();
    match name_section {
        NameSection::Function(x) => func_name_section = x.clone(),
        _ => (),
    }

    let  name_index_map = func_name_section.names(); //used for name section construction
    let mut new_name_index_map = IndexMap::<String>::default();
    let mut imported_func_count: usize;
    
    //parse element section, and add any entry to be exported by main and imported by lazy
    let elem_nodes = log_element_section(&module, &func_list);
    export_candidates.extend(elem_nodes);

//type
    let type_section = module.type_section().unwrap();
    for type_entry in type_section.types() {
        let func_type = match type_entry {
            parity_wasm::elements::Type::Function(ref x) => x,
        };
        let params = func_type.params().to_vec();
        let return_type = func_type.return_type();
        let sig = signature().with_params(params).with_return_type(return_type).build_sig();  
        new_module.push_signature(sig);                  
    }
//data
    let mut new_data_size: usize = 0;
    let data_section = module.data_section().unwrap();
    let data_segments = parse_data_section(data_section, &lazy_nodes, &data_list, is_lazy);
    for seg in data_segments {
        new_module = new_module.with_data_segment(seg);  
    }
    for seg in data_section.entries() {
        new_data_size += seg.value().len(); //counting the size of data segment
    }

    let min_mem_size = ((STACK_ADDR + new_data_size as i32) as f64 / PAGE_SIZE as f64).ceil() as u32;

//import
    let import_section = module.import_section().unwrap();
    imported_func_count = parse_import_section(&mut new_module, &import_section, &type_section);
    // doing this here, because it maybe the case that no import section be present, 
    // but we want to have import section in output anyways
    if !is_lazy {   //add lazy_roots
        // imported_func_count = push_import_candidates_to_module(&module, &mut new_module, &lazy_nodes, func_name_map, imported_func_count, "lazy", &mut import_func_map);
    }
    else {  // add nodes from main.wasm and main.memory, main.stack

        let external = parity_wasm::elements::External::Memory(parity_wasm::elements::MemoryType::new(min_mem_size, None) );
        let import_mem = parity_wasm::elements::ImportEntry::new(String::from("main"), String::from("memory"), external);
        new_module.push_import(import_mem);

        let external = parity_wasm::elements::External::Global(
            parity_wasm::elements::GlobalType::new(parity_wasm::elements::ValueType::I32, true)
        );
        let import_stack = parity_wasm::elements::ImportEntry::new(String::from("main"), String::from("stack"), external);
        new_module.push_import(import_stack);
        imported_func_count = push_import_candidates_to_module(&module, &mut new_module, &export_candidates, func_name_map, imported_func_count, "main", &mut import_func_map);
    }

    match_func_id.extend(import_func_map.iter());
//code
    // let code_section = module.code_section().unwrap();
    let funcs = parse_code_section(module, &lazy_nodes, &func_list, 
                    &mut match_func_id, imported_func_count, env_dependant_funcs, &name_index_map, &mut new_name_index_map, is_lazy);
    for func in funcs {
        new_module.push_function(func);
    }


//export
    //let export_section = module.export_section().unwrap();
    let mut exported_nodes: HashSet<Node> = HashSet::new();
    let mut export_entries = match module.export_section() {
        Some(export_section) => 
        parse_export_section(export_section, &lazy_nodes, func_list, data_list, &mut exported_nodes, &match_func_id, is_lazy),
        None => Vec::new(), //there were no export section!
    };
    if !is_lazy {
        export_entries.extend(push_export_candidates(export_candidates, &mut exported_nodes, func_name_map, &match_func_id));
        //manually export __run__ and Memory and run_load_callback()
        let new_run_id = *match_func_id.get(&old_run_id).unwrap();
        let new_callback_id = *match_func_id.get(&old_callback_id).unwrap();
        let run_exp_entry = parity_wasm::elements::ExportEntry::new(String::from("__run__"), parity_wasm::elements::Internal::Function(new_run_id)); 
        let callback_exp_entry = parity_wasm::elements::ExportEntry::new(String::from("run_load_callback"), parity_wasm::elements::Internal::Function(new_callback_id));   
        let mem_exp_entry = parity_wasm::elements::ExportEntry::new(String::from("memory"), parity_wasm::elements::Internal::Memory(0)); 
        let tbl_exp_entry = parity_wasm::elements::ExportEntry::new(String::from("table"), parity_wasm::elements::Internal::Table(0)); 
        let stck_exp_entry = parity_wasm::elements::ExportEntry::new(String::from("stack"), parity_wasm::elements::Internal::Global(0));
        //^^ better to be logged in exported_nodes as well
        export_entries.extend(vec![run_exp_entry, callback_exp_entry, mem_exp_entry, tbl_exp_entry, stck_exp_entry]);     
    }
    else {  //export lazy nodes
        export_entries.extend(push_export_candidates(lazy_nodes, &mut exported_nodes, func_name_map, &match_func_id));
    }
    for entry in export_entries {
        new_module.push_export(entry);
    }

//global
    //add stack poinrter as global for main.wasm
    if !is_lazy{
        let global_stack = parity_wasm::elements::GlobalEntry::new(
            parity_wasm::elements::GlobalType::new(parity_wasm::elements::ValueType::I32, true), 
            parity_wasm::elements::InitExpr::new(vec![Instruction::I32Const(STACK_ADDR), Instruction::End]));
        new_module = new_module.with_global(global_stack);
    }
    match module.global_section() {
        Some(global_section) => {
            for glob in global_section.entries() {
                new_module = new_module.with_global(glob.clone());
            }
        }  
        None => ()  
    }


///////
println!("printing new index map" );
for ent in new_name_index_map.iter() {
    println!("{:?}", ent );
}
// let mut new_name_index_map = Some(new_name_index_map);
let mut new_func_name_section = FunctionNameSection::default();
*new_func_name_section.names_mut() = new_name_index_map;
let new_name_section = NameSection::Function(new_func_name_section);
let mut new_name_section = Some(new_name_section);

    for sec in module.sections() {
        match sec {
            // Section::Data(data_section) => {
            //     // let data_segments = parse_data_section(data_section, &lazy_nodes, &data_list, is_lazy);
            //     // for seg in data_segments {
            //     //     new_data_size += seg.value().len(); //counting the size of data segment
            //     //     new_module = new_module.with_data_segment(seg);  
            //     // }
            // }
            Section::Memory(mem) => {
                if !is_lazy {   // for  lazy we import the memory section
                    memory_section = mem.clone();//copy this memory section into main.wasm and lazy
                    
                        let mem_type =  parity_wasm::elements::MemoryType::new(min_mem_size, None);
                        *memory_section.entries_mut() = vec![mem_type];
                        new_module = new_module.memory().build(); //just a dummy memory, to be replaced later by module's memory section
                    }
                // }
            } 

            Section::Table(tl) => {
                table_section = tl.clone();
                let tl_entry = tl.entries();
                let old_size = tl_entry[0].limits();
                let bigger_table_type = parity_wasm::elements::TableType::new(old_size.initial(), Some(old_size.maximum().unwrap()+lazy_func_num));
                //^^we grow the table with the number of lazy functions, so we need the max be set appropriately
                *table_section.entries_mut() = vec![bigger_table_type];

                let mut tl_def = TableDefinition::default();
                let dummy_expr = parity_wasm::elements::InitExpr::new(vec![Instruction::I32Const(0), Instruction::End]);
                let tl_entry = TableEntryDefinition{offset: dummy_expr, values: vec![]};
                tl_def.elements = vec![tl_entry];
                new_module.push_table(tl_def); //this adds a dummy table and element section to be replaced later
            }
            Section::Element(el) => { //this section needs attention: for each entry if the func is in export_candidate, keep it with new id
                    element_section = el.clone();
                    // if !is_lazy { // copy into main.wasm
                        for elem_entry in element_section.entries_mut() {
                            for member in elem_entry.members_mut() {
                                *member = *match_func_id.get(member).unwrap();
                            }
                        }
                // }
                // else {  //is lazy
                //     for elem_entry in element_section.entries_mut() {
                //         for member in elem_entry.members_mut() {
                //             *member = match match_func_id.get(member) {
                //                 Some(x) => *x,
                //                 None => *main_match_func_id.get(member).unwrap()
                //             }
                            
                //         }
                //     }                    
                // }
            }
            Section::Custom(x) => {
                if x.name() == "name" {
                    // println!("{:?}", x);
                    let mut custom = CustomSection::default();
                    *custom.name_mut() = "name".to_string();
                    if let Some(y) = new_name_section.take(){
                        y.serialize(custom.payload_mut());
                    }

                    let new_custom = Section::Custom(custom);
                    new_module = new_module.with_section(new_custom);
                    // new_module = new_module.with_section(sec.clone());
                }
            }
            _ => (), //TODO others
        }
    }
println!("printing func id map" );
for ent in match_func_id.iter() {
    println!("{:?}", ent);
}

    let mut out_mod = new_module.build();
    //post processing sections: memory, table, element
    for sec in out_mod.sections_mut() {
        match sec {
            Section::Memory(ref mut x) => *x = memory_section.clone(),
            Section::Table(ref mut x) => *x = table_section.clone(),
            Section::Element(ref mut x) => *x = element_section.clone(),
            Section::Code(section) => { //look for call to imported funcs, and replace the ids
                for body in section.bodies_mut() {
                    let code = body.code_mut();
                        for insn in code.elements_mut() {
                            match insn {
                                &mut Instruction::Call(callee) => {
                                    match match_func_id.get(&callee) {
                                        Some(x) => *insn = Instruction::Call(*x),
                                        None => (),
                                    }
                                }
                                _ => (), //don't care for other insns
                            }
                        
                    }
                }
            }
            _ => ()
        }
    }
    // if !is_lazy {
    //     *main_match_func_id = match_func_id.clone();
    // }
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

fn log_element_section(module: &Module, func_entry_list: &Vec<FuncEntry>) -> HashSet<Node> {
    let element_section = module.elements_section().unwrap();
    let mut node_log: HashSet<Node> = HashSet::new();
    for seg in element_section.entries() {
        for member in seg.members() {
            node_log.insert(Node::Func(func_entry_list[*member as usize]));
        }
    }
    return node_log; 
}
fn parse_import_section(new_module: &mut ModuleBuilder, import_section: &ImportSection, type_section: &TypeSection) -> usize {
    let type_list = type_section.types();
    let mut imported_func_num: usize = 0;
    for entry in import_section.entries() {    //add any importEntry from original module
                    // import_entries.push(entry.clone());
        let mut entry_clone = entry.clone();
        // if entry.module() == "env"{ //skip any env import
        //     continue;
        // }
        if entry.field() == "__stack_pointer" { //skip importing mutable global
            continue;
        }
        match entry.external() {
            parity_wasm::elements::External::Function(ref old_type_index) => {
                imported_func_num += 1;
                let type_entry = &type_list[*old_type_index as usize];
                let func_type = match type_entry {
                    parity_wasm::elements::Type::Function(ref x) => x,
                };
                let params = func_type.params().to_vec();
                let return_type = func_type.return_type();
                let sig = signature().with_params(params).with_return_type(return_type).build_sig();
                let new_type_index = new_module.push_signature(sig);
                *entry_clone.external_mut() = parity_wasm::elements::External::Function(new_type_index);
                new_module.push_import(entry_clone);    //push to new wasm
            }
            parity_wasm::elements::External::Global(glob_entry) => {
                if glob_entry.content_type() == parity_wasm::elements::ValueType::I32 &&
                    glob_entry.is_mutable() == false { //Do not import env.stack
                        ;
                    }     
                else {
                    new_module.push_import(entry_clone);
                }      
            }
            _ => { new_module.push_import(entry_clone); } //push anything else
        }
            
    }
    return imported_func_num
}
fn push_import_candidates_to_module(original_module: &Module, new_module: &mut ModuleBuilder, node_set: &HashSet<Node>,
                                    func_name_map: &NameMap, imported_func_num: usize, imp_module_name: &str, imported_map: &mut HashMap<u32, u32>) -> usize {
    //let mut out_list: Vec<ImportEntry> = Vec::new();
    // let global_section = original_module.global_section().unwrap();
    let function_section = original_module.function_section().unwrap();
    let function_section_entries = function_section.entries();
    let type_section = original_module.type_section().unwrap();
    let mut new_func_id = imported_func_num;
    let mut memory_already_add = false;

    for node in node_set {
        let mut import_entry = parity_wasm::elements::ImportEntry::new(String::from(imp_module_name), String::from("field_tbd"), 
            parity_wasm::elements::External::Function(0));
        match node {
            Node::Func(x) => {
                //there is a difference between func.id vs func.index: id is function index space (used by call ir Element)
                // while idx is in function section space (meaning that which function body corresponds to this func)
                let old_func_id = (*x).id();
                let old_func_index = (*x).index();
                assert!(old_func_index >= 0);
                let func = function_section_entries[old_func_index as usize];
                let type_index = func.type_ref();
                let type_entry = &type_section.types()[type_index as usize];
                let func_type = match type_entry {
                    parity_wasm::elements::Type::Function(ref x) => x,
                    };
                let params = func_type.params().to_vec();
                let return_type = func_type.return_type();
                let sig = signature().with_params(params).with_return_type(return_type).build_sig();                
                // push the new type into the new module and use it as ref in import entry
                let new_type_idx = new_module.push_signature(sig);
                *import_entry.external_mut() = parity_wasm::elements::External::Function(new_type_idx);
                *import_entry.field_mut() = func_name_map.get(old_func_id).unwrap().to_string();
                new_module.push_import(import_entry);
                // println!("import entry {}", new_func_idx);
                imported_map.insert(old_func_id, new_func_id as u32);
                new_func_id += 1;
                //  out_list.push(import_entry.clone());
            }
            Node::Mem(_x) => { 
                // if memory_already_add {
                //     continue;
                // }
                // *import_entry.field_mut() = String::from("memory");
                // *import_entry.external_mut() = parity_wasm::elements::External::Memory(
                //      parity_wasm::elements::MemoryType::new(16, None) );
                // new_module.push_import(import_entry);
                // memory_already_add = true;
                // *memory_imported = true;
            }
            Node::Global(x) => { // having the same global section for both wasms, but check for stack pointer
/*                let glob_entry = &global_section.entries()[x.index() as usize];
                let glob_type = glob_entry.global_type();
                if glob_type.content_type() == parity_wasm::elements::ValueType::I32 &&
                glob_type.is_mutable() == false { // make an import for glob[0] = stack pointer
                    *import_entry.field_mut() = String::from("__stack_pointer");
                    *import_entry.external_mut() = parity_wasm::elements::External::Global(
                            parity_wasm::elements::GlobalType::new(parity_wasm::elements::ValueType::I32, true)
                    );  
                } 
                new_module.push_import(import_entry);we may need this if mutable imports are allowed*/
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
    return new_func_id as usize;    //to send back the number of functions imported
    // return out_list;
}

fn parse_export_section(export_section: &ExportSection, lazy_nodes: &HashSet<Node>, func_list: &Vec<FuncEntry>, data_list: &Vec<MemEntry>, 
                        exported_nodes: &mut HashSet<Node>, match_func_id: &HashMap<u32,u32>, is_lazy: bool) -> Vec<parity_wasm::elements::ExportEntry> {
    let mut out_list: Vec<parity_wasm::elements::ExportEntry> = Vec::new();
    let mut node: Node = Node::Func(func_list[0]);
    let mut seen_name: HashSet<String> = HashSet::new();

    for entry in export_section.entries() {
        let export_name = entry.field();
        let mut new_export = parity_wasm::elements::ExportEntry::new(export_name.to_string(), parity_wasm::elements::Internal::Function(0));
        if seen_name.contains(export_name){
            continue;
        }
        match entry.internal() {
            parity_wasm::elements::Internal::Function(x) => {
                node = Node::Func(func_list[*x as usize]); //to be checked in laze_nodes
                let new_id = match match_func_id.get(x) {
                    Some(id) => *id,
                    None => 66666 //>>>???? when I don't have a map for the new id?
                };
                *new_export.internal_mut() = parity_wasm::elements::Internal::Function(new_id);
            },
            parity_wasm::elements::Internal::Memory(x) => { //do nothing, already exported manually
                // node = Node::Mem(data_list[*x as usize]);
                // new_export = entry.clone();
            }
            parity_wasm::elements::Internal::Global(x) => {
                node = Node::Global(GlobalEntry{index: *x});
                new_export = entry.clone();
            }
            parity_wasm::elements::Internal::Table(x) => {//do nothing, already exported manually
                // node = Node::Table(TableEntry{index: *x});
                // new_export = entry.clone();
            }
        }
        if (!is_lazy && !lazy_nodes.contains(&node)) ||
        (is_lazy && lazy_nodes.contains(&node)) {
            match new_export.internal() {   //just double checking
                parity_wasm::elements::Internal::Function(x) => assert!(*x != 66666),
                _ => (),
            }
            out_list.push(new_export);
            exported_nodes.insert(node);
        }
        else {
            // let dummy_exp = parity_wasm::elements::ExportEntry::new(String::from("field_dummy"), parity_wasm::elements::Internal::Function(0));
            // out_list.push(dummy_exp);
        }
        seen_name.insert(export_name.to_string());
    }
    if !is_lazy && !seen_name.contains("table") {
        let table_entry = parity_wasm::elements::ExportEntry::new("table".to_string(), parity_wasm::elements::Internal::Table(0));
        out_list.push(table_entry);
        exported_nodes.insert(Node::Table(TableEntry{index: 0}));
    }
    return out_list;
}
fn push_export_candidates(candidates: &HashSet<Node>, exported_nodes: &mut HashSet<Node>, func_name_map: &NameMap, match_func_id: &HashMap<u32,u32>)
                             -> Vec<parity_wasm::elements::ExportEntry> {
    let mut out_list: Vec<parity_wasm::elements::ExportEntry> = Vec::new();
    let mut counter = 0;
    let mut already_exported_mem = false;
    let mut already_exported_global: HashSet<u32> = HashSet::new();
    let mut function_names_hash: HashMap<String, u32> = HashMap::new();
    for entry in candidates {
        if exported_nodes.contains(entry) {
            continue;
        }
        let mut exp_entry = parity_wasm::elements::ExportEntry::new(String::from(""), parity_wasm::elements::Internal::Function(0));
        match entry {
            Node::Func(x) => {
                let old_id = (*x).id();
                let new_id = *match_func_id.get(&old_id).unwrap();
                let mut name = func_name_map.get(old_id).unwrap().to_string();
                let mut count = 1;
                if function_names_hash.contains_key(&name) {
                    count = *function_names_hash.get(&name).unwrap();
                    println!("Awkward! I saw this export name before: {} {}", name, count);
                    function_names_hash.insert(name.clone(), count+1);
                    name = name + "__" + &count.to_string();
                }
                else {
                    function_names_hash.insert(name.clone(), count+1);
                }
                *exp_entry.field_mut() = name;
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Function(new_id);
                out_list.push(exp_entry.clone());
                exported_nodes.insert(*entry);
            }
            Node::Mem(_x) => {  //no need to process memory, it will be cloned into main and lazy
                // if already_exported_mem {
                //     continue;
                // }
                // *exp_entry.field_mut() = format!("Memory_{}", counter);//String::from("Memory");
                // // counter += 1;
                // *exp_entry.internal_mut() = parity_wasm::elements::Internal::Memory(0); //just memory 0   
                // already_exported_mem = true;
                // out_list.push(exp_entry.clone());
            }
            Node::Global(x) => {
                if already_exported_global.contains(&(*x).index()) || (*x).index() == 0 { //skip on stack pointer as well
                    continue;
                }
                *exp_entry.field_mut() = format!("Global_{}", counter);//String::from("Global_export");
                counter += 1;
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Global((*x).index() );                
                already_exported_global.insert((*x).index());
                out_list.push(exp_entry.clone());
            }
            Node::Table(x) => {
                *exp_entry.field_mut() = String::from("Table_export");
                *exp_entry.internal_mut() = parity_wasm::elements::Internal::Table(0); // just table 0 
                out_list.push(exp_entry.clone());              
            }
        }
        
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
if !is_lazy{
    for (idx, seg) in segments.iter().enumerate() { // is_lazy XNOR contains
        // if (!is_lazy && !lazy_nodes.contains(&Node::Mem(data_list[idx]))) || 
        //  (is_lazy && lazy_nodes.contains(&Node::Mem(data_list[idx]))) {
        //     out_list.push(seg.clone());
        // }
        // else { // is in lazy list: should be NOP, as the initilizer uses it
        //     let dummy_expr = parity_wasm::elements::InitExpr::new(vec![Instruction::I32Const(0) ,Instruction::End]);
        //     let dummy_seg = DataSegment::new(seg.index(), dummy_expr, vec![]);
        //     out_list.push(dummy_seg);
        // }
        out_list.push(seg.clone());     //just copy over the data segments

    }
}
    return out_list;
}
fn parse_code_section(module: &Module,//code: &CodeSection, type_section: &TypeSection, function_section: &FunctionSection,
                    lazy_nodes: &HashSet<Node>, func_list: &Vec<FuncEntry>, match_func_id: &mut HashMap<u32,u32>, 
                    new_imported_count: usize, env_dependant_funcs: &HashSet<u32>, name_index_map: &IndexMap<String>,
                    new_name_index_map: &mut IndexMap<String>, is_lazy: bool) -> Vec<FunctionDefinition> {
    let code = module.code_section().unwrap();
    let type_section = module.type_section().unwrap();
    let function_section = module.function_section().unwrap();
// code_section, type_section, function_section
    let mut out_list: Vec<FunctionDefinition> = Vec::new();
    let ttyy = type_section.types();
    let funcs = function_section.entries();
    let bodies = code.bodies();
    let mut old_imported_count = 0;
    let mut added_func_num = 0;
    for ff in func_list.iter() {
        if ff.index() != -1 {
            break;
        }
        old_imported_count += 1;
    }
    for (idx, func_body) in bodies.iter().enumerate() {
        let old_id = idx + old_imported_count;
        let new_id = added_func_num + new_imported_count;
        if (!is_lazy && !lazy_nodes.contains(&Node::Func(func_list[idx+old_imported_count]))) ||
         (is_lazy && lazy_nodes.contains(&Node::Func(func_list[idx+old_imported_count]))) {  
            if env_dependant_funcs.contains(&(old_id as u32)) { //dymmy body for env dependant funcs
                let empty: Vec<parity_wasm::elements::ValueType> = vec![];
                let sig = signature().with_params(empty).with_return_type(None).build_sig();   
                let unreach_insns = parity_wasm::elements::Instructions::new(
                    vec![Instruction::Unreachable, Instruction::End]
                );
                let func = function().with_signature(sig)
                            .body().with_instructions(unreach_insns).build().build();
                out_list.push(func);
            }
            else {
                let func_entry = funcs[idx];
                let func_type = match ttyy[func_entry.type_ref() as usize] {
                    parity_wasm::elements::Type::Function(ref x) => x,
                };
                let params = func_type.params().to_vec();
                let return_type = func_type.return_type();
                let sig = signature().with_params(params).with_return_type(return_type).build_sig();                
                let func = function().with_signature(sig).with_body(func_body.clone()).build();
                out_list.push(func);
                //update indexMap
                let name = (name_index_map.get(old_id as u32).unwrap());
                new_name_index_map.insert(new_id as u32, name.to_string());
            }
            added_func_num += 1;
            match_func_id.insert(old_id as u32, new_id as u32); //to be used for Export section
        }
        else {  
            // let empty: Vec<parity_wasm::elements::ValueType> = vec![];
            // let sig = signature().with_params(empty).with_return_type(None).build_sig();   
            // let unreach_insns = parity_wasm::elements::Instructions::new(
            //     vec![Instruction::Unreachable, Instruction::End]
            // );
            // let func = function().with_signature(sig)
            //             .body().with_instructions(unreach_insns).build().build();
            // out_list.push(func);
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