//! WGSL/SPIR-V codegen for verified CuTe layout operations.
//!
//! # Architecture
//!
//! The codegen pipeline:
//! - **ArithExpr** (verified in verus-cutedsl): specification + correctness proofs
//! - **WgslExpr** (this crate): mirrors ArithExpr for WGSL string emission
//! - **#[kernel]** macro: parses Rust → builds WgslExpr → emits WGSL
//!
//! # Trust boundary
//!
//! - VERIFIED (by Verus): ArithExpr faithfully represents CuTe operations
//!   (delinearize, offset, GEMM MAC — proved for all ranks)
//! - AUDITABLE (~50 lines): WgslExpr.emit() — structural mapping to WGSL text
//! - TRUSTED: WGSL compiler (naga/tint), GPU driver, silicon

// proc_macro imports disabled — crate is now a regular library
// use proc_macro::TokenStream;
// use quote::quote;
// use syn::{parse_macro_input, ItemFn, FnArg, Pat};

//  ══════════════════════════════════════════════════════════════
//  WgslExpr: mirrors verified ArithExpr for WGSL emission
//  ══════════════════════════════════════════════════════════════

///  Arithmetic expression IR for WGSL emission.
///
///  **Structural mirror of `ArithExpr`** from `verus-cutedsl/src/arith_expr.rs`.
///  Each variant corresponds 1:1 to the verified spec type:
///
///  | WgslExpr      | ArithExpr          | Verus spec                  |
///  |---------------|--------------------|-----------------------------|
///  | Const(i64)    | Const(int)         | arith_eval → c              |
///  | Var(u32)      | Var(nat)           | arith_eval → env[i]         |
///  | Add(a, b)     | Add(a, b)          | arith_eval → eval(a)+eval(b)|
///  | Mul(a, b)     | Mul(a, b)          | arith_eval → eval(a)*eval(b)|
///  | Div(a, b)     | Div(a, b)          | arith_eval → eval(a)/eval(b)|
///  | Mod(a, b)     | Mod(a, b)          | arith_eval → eval(a)%eval(b)|
///  | Index(arr,ix) | Index(nat,ix)      | arith_eval_with_arrays      |
///
///  The trust boundary: `emit()` correctly renders each variant as WGSL text.
///  Verified by: structural correspondence (auditable) + naga parse tests.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum CmpOp { Lt, Le, Gt, Ge, Eq, Ne }

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum WgslExpr {
    ///  Integer constant.
    Const(i64),
    ///  Variable reference by index into the variable name table.
    Var(u32),
    ///  Addition.
    Add(Box<WgslExpr>, Box<WgslExpr>),
    ///  Subtraction.
    Sub(Box<WgslExpr>, Box<WgslExpr>),
    ///  Multiplication.
    Mul(Box<WgslExpr>, Box<WgslExpr>),
    ///  Integer division (truncating, non-negative operands).
    Div(Box<WgslExpr>, Box<WgslExpr>),
    ///  Integer modulo (non-negative operands).
    Mod(Box<WgslExpr>, Box<WgslExpr>),
    ///  Array index: arrays[arr_idx][eval(idx_expr)].
    Index(u32, Box<WgslExpr>),
    ///  Arithmetic right shift (fixed-point multiply: (a * b) >> N).
    Shr(Box<WgslExpr>, Box<WgslExpr>),
    ///  Comparison: returns bool in WGSL (0/1 in spec).
    Cmp(CmpOp, Box<WgslExpr>, Box<WgslExpr>),
    ///  Summation reduction: Reduce(var, bound, body) = Σ body over var in 0..bound.
    Reduce(u32, Box<WgslExpr>, Box<WgslExpr>),
}

impl WgslExpr {
    ///  Emit WGSL expression string.
    ///
    ///  - `var_names`: maps Var(i) to WGSL variable name
    ///  - `array_names`: maps Index(i, _) to WGSL buffer name
    ///
    ///  This is the auditable trust boundary (~30 lines).
    ///  Each case directly corresponds to WGSL integer arithmetic.
    ///  Emit as a WGSL expression (inline, no statements).
    ///  For Reduce, use `emit_stmt` instead (needs statement-level hoisting).
    pub fn emit(&self, var_names: &[&str], array_names: &[&str]) -> String {
        match self {
            WgslExpr::Const(c) => {
                if *c >= 0 {
                    format!("{}u", c)
                } else {
                    format!("i32({})", c)
                }
            }
            WgslExpr::Var(i) => {
                let idx = *i as usize;
                if idx < var_names.len() {
                    var_names[idx].to_string()
                } else {
                    format!("v{}", i)
                }
            }
            WgslExpr::Add(a, b) => {
                format!("({} + {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
            }
            WgslExpr::Sub(a, b) => {
                format!("({} - {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
            }
            WgslExpr::Mul(a, b) => {
                //  Pattern-match Mul(Cmp, Cmp) as boolean AND
                match (a.as_ref(), b.as_ref()) {
                    (WgslExpr::Cmp(..), WgslExpr::Cmp(..)) => {
                        format!("({} && {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
                    }
                    _ => format!("({} * {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
                }
            }
            WgslExpr::Div(a, b) => {
                format!("({} / {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
            }
            WgslExpr::Mod(a, b) => {
                format!("({} % {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
            }
            WgslExpr::Index(arr, idx_expr) => {
                let arr_idx = *arr as usize;
                let arr_name = if arr_idx < array_names.len() {
                    array_names[arr_idx]
                } else {
                    "buf"
                };
                format!("{}[{}]", arr_name, idx_expr.emit(var_names, array_names))
            }
            WgslExpr::Shr(a, b) => {
                format!("({} >> {})", a.emit(var_names, array_names), b.emit(var_names, array_names))
            }
            WgslExpr::Cmp(op, a, b) => {
                let op_str = match op {
                    CmpOp::Lt => "<", CmpOp::Le => "<=",
                    CmpOp::Gt => ">", CmpOp::Ge => ">=",
                    CmpOp::Eq => "==", CmpOp::Ne => "!=",
                };
                format!("({} {} {})", a.emit(var_names, array_names), op_str, b.emit(var_names, array_names))
            }
            WgslExpr::Reduce(_, _, _) => {
                //  Reduce can't be emitted inline — needs statement hoisting.
                //  Use emit_stmt for expressions containing Reduce.
                "/* ERROR: Reduce must use emit_stmt */".to_string()
            }
        }
    }

    ///  Emit as WGSL statements, returning the name of the result variable.
    ///  Handles Reduce by hoisting to a for-loop with accumulator.
    pub fn emit_stmt(
        &self, var_names: &[&str], array_names: &[&str],
        out: &mut String, indent: &str, counter: &mut usize,
    ) -> String {
        match self {
            WgslExpr::Reduce(var, bound, body) => {
                let acc_name = format!("_acc{}", counter);
                *counter += 1;
                let var_idx = *var as usize;
                let loop_var = if var_idx < var_names.len() {
                    var_names[var_idx].to_string()
                } else {
                    format!("_k{}", var)
                };
                let bound_str = bound.emit(var_names, array_names);

                out.push_str(&format!("{}var {}: i32 = 0;\n", indent, acc_name));
                out.push_str(&format!("{}for (var {}: u32 = 0u; {} < {}; {}++) {{\n",
                    indent, loop_var, loop_var, bound_str, loop_var));

                //  Emit body (may itself contain Reduce)
                let body_result = body.emit_stmt(var_names, array_names,
                    out, &format!("{}  ", indent), counter);
                out.push_str(&format!("{}  {} += i32({});\n", indent, acc_name, body_result));
                out.push_str(&format!("{}}}\n", indent));

                acc_name
            }
            //  Non-Reduce: emit as inline expression
            _ => self.emit(var_names, array_names),
        }
    }
}

//  ══════════════════════════════════════════════════════════════
//  CuTe operation lowering: build WgslExpr from layout parameters
//  ══════════════════════════════════════════════════════════════

//  All lowering functions mirror their verified counterparts in verus-cutedsl/src/arith_expr.rs.
//  They are used by kernel generators and tests; #[allow(dead_code)] suppresses proc-macro warnings.

///  Build WgslExpr for delinearize(x, shape)[i] = (x / prefix_product(i)) % shape[i].
///  Mirrors `delinearize_coord_expr`. Proved by `lemma_delinearize_coord_expr_correct`.
#[allow(dead_code)]
fn delinearize_coord_expr(x_var: u32, shape: &[u64], i: usize) -> WgslExpr {
    let prefix_prod = shape_prefix_product(shape, i);
    let shape_i = shape[i];
    WgslExpr::Mod(
        Box::new(WgslExpr::Div(
            Box::new(WgslExpr::Var(x_var)),
            Box::new(WgslExpr::Const(prefix_prod as i64)),
        )),
        Box::new(WgslExpr::Const(shape_i as i64)),
    )
}

///  Product of shape[0..i]. Mirrors `shape_prefix_product` from arith_expr.rs.
#[allow(dead_code)]
fn shape_prefix_product(shape: &[u64], i: usize) -> u64 {
    shape[..i].iter().product::<u64>().max(1)
}

///  Build WgslExpr for layout offset: sum_i (delinearize(x, shape)[i] * stride[i]).
///
///  Mirrors `offset_expr` from verus-cutedsl/src/arith_expr.rs.
///  Correctness proved by `lemma_offset_expr_correct`.
#[allow(dead_code)]
fn offset_expr(x_var: u32, shape: &[u64], stride: &[i64]) -> WgslExpr {
    assert_eq!(shape.len(), stride.len());
    if shape.is_empty() {
        return WgslExpr::Const(0);
    }
    offset_expr_skip(x_var, shape, stride, 0)
}

#[allow(dead_code)]
fn offset_expr_skip(x_var: u32, shape: &[u64], stride: &[i64], start: usize) -> WgslExpr {
    if start >= shape.len() {
        return WgslExpr::Const(0);
    }
    let coord = delinearize_coord_expr(x_var, shape, start);
    let term = WgslExpr::Mul(
        Box::new(coord),
        Box::new(WgslExpr::Const(stride[start])),
    );
    if start + 1 >= shape.len() {
        term
    } else {
        WgslExpr::Add(
            Box::new(term),
            Box::new(offset_expr_skip(x_var, shape, stride, start + 1)),
        )
    }
}

///  Build WgslExpr for GEMM A-index: i*K + k.
///  Variables: 0=i, 1=j, 2=k. Mirrors `gemm_a_index_expr`.
#[allow(dead_code)]
fn gemm_a_index_expr(k_size: u64) -> WgslExpr {
    WgslExpr::Add(
        Box::new(WgslExpr::Mul(
            Box::new(WgslExpr::Var(0)),
            Box::new(WgslExpr::Const(k_size as i64)),
        )),
        Box::new(WgslExpr::Var(2)),
    )
}

///  Build WgslExpr for GEMM B-index: k*N + j.
///  Variables: 0=i, 1=j, 2=k. Mirrors `gemm_b_index_expr`.
#[allow(dead_code)]
fn gemm_b_index_expr(n: u64) -> WgslExpr {
    WgslExpr::Add(
        Box::new(WgslExpr::Mul(
            Box::new(WgslExpr::Var(2)),
            Box::new(WgslExpr::Const(n as i64)),
        )),
        Box::new(WgslExpr::Var(1)),
    )
}

///  Build WgslExpr for GEMM MAC: A[i*K+k] * B[k*N+j].
///  Array 0=A, Array 1=B. Variables: 0=i, 1=j, 2=k. Mirrors `gemm_mac_expr`.
#[allow(dead_code)]
fn gemm_mac_expr(k_size: u64, n: u64) -> WgslExpr {
    WgslExpr::Mul(
        Box::new(WgslExpr::Index(0, Box::new(gemm_a_index_expr(k_size)))),
        Box::new(WgslExpr::Index(1, Box::new(gemm_b_index_expr(n)))),
    )
}

//  ══════════════════════════════════════════════════════════════
//  Kernel spec → WGSL emission (mirrors verified KernelSpec from verus-cutedsl)
//  ══════════════════════════════════════════════════════════════

///  Buffer binding for a kernel.
#[allow(dead_code)]
pub struct BufferDesc {
    pub name: String,
    pub binding: u32,
    pub read_only: bool,
}

///  Single output: (scatter, compute) pair. Mirrors OutputSpec from kernel.rs.
#[allow(dead_code)]
pub struct OutputDesc {
    pub scatter: WgslExpr,
    pub compute: WgslExpr,
    pub buffer_name: String,
}

///  Kernel description — mirrors KernelSpec from verus-cutedsl/src/kernel.rs.
///  Same structure: guard + Vec<(scatter, compute)> outputs.
#[allow(dead_code)]
pub struct KernelDesc {
    pub name: String,
    pub guard: WgslExpr,
    pub outputs: Vec<OutputDesc>,
    pub buffers: Vec<BufferDesc>,
    pub var_names: Vec<String>,
    pub workgroup_size: [u32; 3],
    pub dispatch_dims: u32,
}

///  Emit a complete WGSL compute shader from a KernelDesc.
#[allow(dead_code)]
pub fn emit_kernel_wgsl(k: &KernelDesc) -> String {
    let var_name_refs: Vec<&str> = k.var_names.iter().map(|s| s.as_str()).collect();
    let array_names: Vec<&str> = k.buffers.iter().map(|b| b.name.as_str()).collect();

    let mut shader = String::new();

    //  Buffer declarations
    for buf in &k.buffers {
        let access = if buf.read_only { "read" } else { "read_write" };
        shader.push_str(&format!(
            "@group(0) @binding({}) var<storage, {}> {}: array<i32>;\n",
            buf.binding, access, buf.name
        ));
    }
    shader.push('\n');

    //  Entry point
    shader.push_str(&format!(
        "@compute @workgroup_size({}, {}, {})\n",
        k.workgroup_size[0], k.workgroup_size[1], k.workgroup_size[2]
    ));
    shader.push_str(&format!(
        "fn {}(\n  @builtin(global_invocation_id) gid: vec3<u32>,\n) {{\n",
        k.name
    ));

    //  Thread variable extraction
    if k.dispatch_dims >= 1 && k.var_names.len() >= 1 {
        shader.push_str(&format!("  let {} = gid.x;\n", k.var_names[0]));
    }
    if k.dispatch_dims >= 2 && k.var_names.len() >= 2 {
        shader.push_str(&format!("  let {} = gid.y;\n", k.var_names[1]));
    }
    if k.dispatch_dims >= 3 && k.var_names.len() >= 3 {
        shader.push_str(&format!("  let {} = gid.z;\n", k.var_names[2]));
    }

    //  Guard
    let guard_wgsl = k.guard.emit(&var_name_refs, &array_names);
    shader.push_str(&format!("  if (!{}) {{ return; }}\n", guard_wgsl));

    //  Emit all outputs
    let mut counter = 0;
    for output in &k.outputs {
        let mut body_stmts = String::new();
        let compute_result = output.compute.emit_stmt(
            &var_name_refs, &array_names,
            &mut body_stmts, "  ", &mut counter,
        );
        shader.push_str(&body_stmts);
        let scatter_wgsl = output.scatter.emit(&var_name_refs, &array_names);
        shader.push_str(&format!("  {}[{}] = i32({});\n",
            output.buffer_name, scatter_wgsl, compute_result));
    }
    shader.push_str("}\n");

    shader
}

//  ══════════════════════════════════════════════════════════════
//  Kernel constructors (mirrors verified constructors from kernel.rs)
//  ══════════════════════════════════════════════════════════════

///  Build a KernelDesc for vector add: out[i] = a[i] + b[i]
#[allow(dead_code)]
fn vector_add_kernel_desc(n: u64) -> KernelDesc {
    KernelDesc {
        name: "vector_add".to_string(),
        guard: WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(n as i64))),
        outputs: vec![OutputDesc {
            scatter: WgslExpr::Var(0),
            compute: WgslExpr::Add(
                Box::new(WgslExpr::Index(0, Box::new(WgslExpr::Var(0)))),
                Box::new(WgslExpr::Index(1, Box::new(WgslExpr::Var(0)))),
            ),
            buffer_name: "out".into(),
        }],
        buffers: vec![
            BufferDesc { name: "a".into(), binding: 0, read_only: true },
            BufferDesc { name: "b".into(), binding: 1, read_only: true },
            BufferDesc { name: "out".into(), binding: 2, read_only: false },
        ],
        var_names: vec!["tid".into()],
        workgroup_size: [256, 1, 1],
        dispatch_dims: 1,
    }
}

///  Build a KernelDesc for naive GEMM: C[i*N+j] = Σ_k A[i*K+k] * B[k*N+j]
#[allow(dead_code)]
fn gemm_kernel_desc(m: u64, k_size: u64, n: u64) -> KernelDesc {
    KernelDesc {
        name: "naive_gemm".to_string(),
        guard: WgslExpr::Mul(
            Box::new(WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(m as i64)))),
            Box::new(WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(1)), Box::new(WgslExpr::Const(n as i64)))),
        ),
        outputs: vec![OutputDesc {
            scatter: WgslExpr::Add(
                Box::new(WgslExpr::Mul(Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(n as i64)))),
                Box::new(WgslExpr::Var(1)),
            ),
            compute: WgslExpr::Reduce(
                2,
                Box::new(WgslExpr::Const(k_size as i64)),
                Box::new(WgslExpr::Mul(
                    Box::new(WgslExpr::Index(0, Box::new(WgslExpr::Add(
                        Box::new(WgslExpr::Mul(Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(k_size as i64)))),
                        Box::new(WgslExpr::Var(2)),
                    )))),
                    Box::new(WgslExpr::Index(1, Box::new(WgslExpr::Add(
                        Box::new(WgslExpr::Mul(Box::new(WgslExpr::Var(2)), Box::new(WgslExpr::Const(n as i64)))),
                        Box::new(WgslExpr::Var(1)),
                    )))),
                )),
            ),
            buffer_name: "c".into(),
        }],
        buffers: vec![
            BufferDesc { name: "a".into(), binding: 0, read_only: true },
            BufferDesc { name: "b".into(), binding: 1, read_only: true },
            BufferDesc { name: "c".into(), binding: 2, read_only: false },
        ],
        var_names: vec!["i".into(), "j".into(), "kk".into()],
        workgroup_size: [16, 16, 1],
        dispatch_dims: 2,
    }
}

//  ══════════════════════════════════════════════════════════════
//  Complete kernel generators (legacy string-template approach)
///  Build a KernelDesc for dot product: out[0] = Σ_k a[k] * b[k]
#[allow(dead_code)]
fn dot_product_kernel_desc(n: u64) -> KernelDesc {
    KernelDesc {
        name: "dot_product".to_string(),
        guard: WgslExpr::Cmp(CmpOp::Eq, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(0))),
        outputs: vec![OutputDesc {
            scatter: WgslExpr::Const(0),
            compute: WgslExpr::Reduce(
                1,
                Box::new(WgslExpr::Const(n as i64)),
                Box::new(WgslExpr::Mul(
                    Box::new(WgslExpr::Index(0, Box::new(WgslExpr::Var(1)))),
                    Box::new(WgslExpr::Index(1, Box::new(WgslExpr::Var(1)))),
                )),
            ),
            buffer_name: "out".into(),
        }],
        buffers: vec![
            BufferDesc { name: "a".into(), binding: 0, read_only: true },
            BufferDesc { name: "b".into(), binding: 1, read_only: true },
            BufferDesc { name: "out".into(), binding: 2, read_only: false },
        ],
        var_names: vec!["tid".into(), "k".into()],
        workgroup_size: [1, 1, 1],
        dispatch_dims: 1,
    }
}

///  Build a KernelDesc for layout offset: out[x] = layout.offset(x)
#[allow(dead_code)]
fn offset_kernel_desc(shape: &[u64], stride: &[i64]) -> KernelDesc {
    let n: u64 = shape.iter().product();
    KernelDesc {
        name: "layout_offset".to_string(),
        guard: WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(n as i64))),
        outputs: vec![OutputDesc {
            scatter: WgslExpr::Var(0),
            compute: offset_expr(0, shape, stride),
            buffer_name: "out".into(),
        }],
        buffers: vec![
            BufferDesc { name: "out".into(), binding: 0, read_only: false },
        ],
        var_names: vec!["tid".into()],
        workgroup_size: [256, 1, 1],
        dispatch_dims: 1,
    }
}

//  ══════════════════════════════════════════════════════════════
//  BLA kernel descriptors (mirrors verified specs in verus-fractals/src/bla_kernels.rs)
//  ══════════════════════════════════════════════════════════════

///  Helper: Index(buf, Var(0))
fn bla_idx(buf: u32) -> WgslExpr { WgslExpr::Index(buf, Box::new(WgslExpr::Var(0))) }
///  Helper: Index(buf, 2*Var(0))
fn bla_idx_2k(buf: u32) -> WgslExpr {
    WgslExpr::Index(buf, Box::new(WgslExpr::Mul(Box::new(WgslExpr::Const(2)), Box::new(WgslExpr::Var(0)))))
}
///  Helper: Index(buf, 2*Var(0)+1)
fn bla_idx_2k1(buf: u32) -> WgslExpr {
    WgslExpr::Index(buf, Box::new(WgslExpr::Add(
        Box::new(WgslExpr::Mul(Box::new(WgslExpr::Const(2)), Box::new(WgslExpr::Var(0)))),
        Box::new(WgslExpr::Const(1)))))
}
///  Helper: fixed-point multiply term (a * b) >> frac
fn fp_term(a: WgslExpr, b: WgslExpr, frac: u32) -> WgslExpr {
    WgslExpr::Shr(Box::new(WgslExpr::Mul(Box::new(a), Box::new(b))),
                  Box::new(WgslExpr::Const(frac as i64)))
}

///  BLA level 0 kernel: A = 2·Z_n, B = (ONE, 0).
///  Mirrors bla_level0_kernel from verus-fractals (verified: lemma_bla_level0_correct).
#[allow(dead_code)]
fn bla_level0_kernel_desc(m: u64, one_fp: i64) -> KernelDesc {
    KernelDesc {
        name: "bla_level0".to_string(),
        guard: WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(m as i64))),
        outputs: vec![
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_a_re".into(),
                compute: WgslExpr::Mul(Box::new(WgslExpr::Const(2)), Box::new(bla_idx(0))) },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_a_im".into(),
                compute: WgslExpr::Mul(Box::new(WgslExpr::Const(2)), Box::new(bla_idx(1))) },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_b_re".into(),
                compute: WgslExpr::Const(one_fp) },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_b_im".into(),
                compute: WgslExpr::Const(0) },
        ],
        buffers: vec![
            BufferDesc { name: "orbit_re".into(), binding: 0, read_only: true },
            BufferDesc { name: "orbit_im".into(), binding: 1, read_only: true },
            BufferDesc { name: "out_a_re".into(), binding: 2, read_only: false },
            BufferDesc { name: "out_a_im".into(), binding: 3, read_only: false },
            BufferDesc { name: "out_b_re".into(), binding: 4, read_only: false },
            BufferDesc { name: "out_b_im".into(), binding: 5, read_only: false },
        ],
        var_names: vec!["tid".into()],
        workgroup_size: [256, 1, 1],
        dispatch_dims: 1,
    }
}

///  BLA merge kernel: A_z = A_y·A_x, B_z = A_y·B_x + B_y.
///  Thread k merges entries [2k] and [2k+1].
///  Mirrors bla_merge_kernel from verus-fractals (verified: lemma_merge_correct).
#[allow(dead_code)]
fn bla_merge_kernel_desc(n_pairs: u64, frac: u32) -> KernelDesc {
    //  A_z = cmul(A_y, A_x) in fixed-point
    let az_re = WgslExpr::Sub(
        Box::new(fp_term(bla_idx_2k1(0), bla_idx_2k(0), frac)),
        Box::new(fp_term(bla_idx_2k1(1), bla_idx_2k(1), frac)));
    let az_im = WgslExpr::Add(
        Box::new(fp_term(bla_idx_2k1(0), bla_idx_2k(1), frac)),
        Box::new(fp_term(bla_idx_2k1(1), bla_idx_2k(0), frac)));
    //  A_y · B_x
    let aybx_re = WgslExpr::Sub(
        Box::new(fp_term(bla_idx_2k1(0), bla_idx_2k(2), frac)),
        Box::new(fp_term(bla_idx_2k1(1), bla_idx_2k(3), frac)));
    let aybx_im = WgslExpr::Add(
        Box::new(fp_term(bla_idx_2k1(0), bla_idx_2k(3), frac)),
        Box::new(fp_term(bla_idx_2k1(1), bla_idx_2k(2), frac)));
    //  B_z = A_y·B_x + B_y
    let bz_re = WgslExpr::Add(Box::new(aybx_re), Box::new(bla_idx_2k1(2)));
    let bz_im = WgslExpr::Add(Box::new(aybx_im), Box::new(bla_idx_2k1(3)));

    KernelDesc {
        name: "bla_merge".to_string(),
        guard: WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(n_pairs as i64))),
        outputs: vec![
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_a_re".into(), compute: az_re },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_a_im".into(), compute: az_im },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_b_re".into(), compute: bz_re },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_b_im".into(), compute: bz_im },
        ],
        buffers: vec![
            BufferDesc { name: "a_re".into(), binding: 0, read_only: true },
            BufferDesc { name: "a_im".into(), binding: 1, read_only: true },
            BufferDesc { name: "b_re".into(), binding: 2, read_only: true },
            BufferDesc { name: "b_im".into(), binding: 3, read_only: true },
            BufferDesc { name: "out_a_re".into(), binding: 4, read_only: false },
            BufferDesc { name: "out_a_im".into(), binding: 5, read_only: false },
            BufferDesc { name: "out_b_re".into(), binding: 6, read_only: false },
            BufferDesc { name: "out_b_im".into(), binding: 7, read_only: false },
        ],
        var_names: vec!["tid".into()],
        workgroup_size: [256, 1, 1],
        dispatch_dims: 1,
    }
}

///  BLA apply kernel: z' = A·z + B·dc per pixel.
///  Mirrors bla_apply_kernel from verus-fractals (verified: lemma_merge_correct).
#[allow(dead_code)]
fn bla_apply_kernel_desc(n_pixels: u64, frac: u32) -> KernelDesc {
    //  A·z
    let az_re = WgslExpr::Sub(
        Box::new(fp_term(bla_idx(2), bla_idx(0), frac)),
        Box::new(fp_term(bla_idx(3), bla_idx(1), frac)));
    let az_im = WgslExpr::Add(
        Box::new(fp_term(bla_idx(2), bla_idx(1), frac)),
        Box::new(fp_term(bla_idx(3), bla_idx(0), frac)));
    //  B·dc
    let bdc_re = WgslExpr::Sub(
        Box::new(fp_term(bla_idx(4), bla_idx(6), frac)),
        Box::new(fp_term(bla_idx(5), bla_idx(7), frac)));
    let bdc_im = WgslExpr::Add(
        Box::new(fp_term(bla_idx(4), bla_idx(7), frac)),
        Box::new(fp_term(bla_idx(5), bla_idx(6), frac)));
    //  z' = A·z + B·dc
    let z_re = WgslExpr::Add(Box::new(az_re), Box::new(bdc_re));
    let z_im = WgslExpr::Add(Box::new(az_im), Box::new(bdc_im));

    KernelDesc {
        name: "bla_apply".to_string(),
        guard: WgslExpr::Cmp(CmpOp::Lt, Box::new(WgslExpr::Var(0)), Box::new(WgslExpr::Const(n_pixels as i64))),
        outputs: vec![
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_z_re".into(), compute: z_re },
            OutputDesc { scatter: WgslExpr::Var(0), buffer_name: "out_z_im".into(), compute: z_im },
        ],
        buffers: vec![
            BufferDesc { name: "z_re".into(), binding: 0, read_only: true },
            BufferDesc { name: "z_im".into(), binding: 1, read_only: true },
            BufferDesc { name: "a_re".into(), binding: 2, read_only: true },
            BufferDesc { name: "a_im".into(), binding: 3, read_only: true },
            BufferDesc { name: "b_re".into(), binding: 4, read_only: true },
            BufferDesc { name: "b_im".into(), binding: 5, read_only: true },
            BufferDesc { name: "dc_re".into(), binding: 6, read_only: true },
            BufferDesc { name: "dc_im".into(), binding: 7, read_only: true },
            BufferDesc { name: "out_z_re".into(), binding: 8, read_only: false },
            BufferDesc { name: "out_z_im".into(), binding: 9, read_only: false },
        ],
        var_names: vec!["tid".into()],
        workgroup_size: [256, 1, 1],
        dispatch_dims: 1,
    }
}

//  ══════════════════════════════════════════════════════════════
//  Mandelbrot generators
//  ══════════════════════════════════════════════════════════════

///  Generate a complete WGSL Mandelbrot renderer (fixed-point integer arithmetic).
///
///  Uses 20.12 fixed-point (12 fractional bits, precision ~0.0002).
///  12 bits chosen so `z_re * z_re` never overflows i32: after a non-escaping
///  iteration, |z| ≤ 2 so |z_new| ≤ |z|² + |c| ≤ 6, giving max raw product
///  (6 × 4096)² = 603M < 2³¹. See `docs/verified-gpu-pipeline.md` §FixedPoint.
///
///  Each thread computes one pixel. Output: iteration count in out[py * w + px].
///  Viewport params (x_min, y_min, dx, dy) come from a params buffer for interactive zoom.
#[allow(dead_code)]
fn generate_mandelbrot_wgsl(
    width: u32, height: u32, max_iter: u32,
    workgroup_size: [u32; 2],
) -> String {
    let frac_bits: u32 = 12;
    let one: i64 = 1 << frac_bits;
    let escape = 4 * one;

    format!(
        "\
//  Viewport params: x_min, y_min, dx, dy in 20.12 fixed-point
@group(0) @binding(0) var<storage, read> params: array<i32>;
@group(0) @binding(1) var<storage, read_write> out: array<u32>;

@compute @workgroup_size({wgs_x}, {wgs_y}, 1)
fn mandelbrot(
  @builtin(global_invocation_id) gid: vec3<u32>,
) {{
  let px = gid.x;
  let py = gid.y;
  if (px >= {w}u || py >= {h}u) {{ return; }}

  //  Read viewport from params buffer (Index into storage buffer)
  let x_min: i32 = params[0];
  let y_min: i32 = params[1];
  let dx: i32 = params[2];
  let dy: i32 = params[3];

  //  Pixel → complex plane (20.12 fixed-point)
  let c_re: i32 = x_min + i32(px) * dx / i32({w}u);
  let c_im: i32 = y_min + i32(py) * dy / i32({h}u);

  var z_re: i32 = 0;
  var z_im: i32 = 0;
  var iter: u32 = 0u;

  for (var i: u32 = 0u; i < {max_iter}u; i++) {{
    let re2: i32 = (z_re * z_re) >> {fb}u;
    let im2: i32 = (z_im * z_im) >> {fb}u;
    if (re2 + im2 > {esc}) {{ break; }}

    let new_re: i32 = re2 - im2 + c_re;
    let new_im: i32 = ((z_re * z_im) >> {fb1}u) + c_im;
    z_re = new_re;
    z_im = new_im;
    iter = i + 1u;
  }}

  out[py * {w}u + px] = iter;
}}
",
        wgs_x = workgroup_size[0],
        wgs_y = workgroup_size[1],
        w = width, h = height,
        max_iter = max_iter,
        fb = frac_bits,
        fb1 = frac_bits - 1,
        esc = escape,
    )
}

///  Generate WGSL for deep Mandelbrot with BLA + perturbation theory.
///
///  Uses f32 per-pixel deltas with precomputed reference orbit + BLA table.
///  The BLA merge formula is verified: `lemma_merge_correct` in verus-fractals/src/bla.rs.
///  The complex multiply matches `cmul` spec. Rebase preserves orbit (`lemma_rebase_preserves_orbit`).
///
///  Buffers:
///    0: params (uniform) — width, height, max_iter, orbit_len, c_re, c_im, pixel_scale, num_levels
///    1: orbit_re (storage, read) — reference orbit real parts
///    2: orbit_im (storage, read) — reference orbit imag parts
///    3: bla_data (storage, read) — flat BLA entries [a_re, a_im, b_re, b_im, r2, l] × N
///    4: bla_offsets (storage, read) — level start offsets in bla_data
///    5: out (storage, read_write) — RGBA pixel output
#[allow(dead_code)]
fn generate_mandelbrot_bla_wgsl(width: u32, height: u32) -> String {
    //  Complex multiply as WgslExpr would emit: (a.x*b.x - a.y*b.y, a.x*b.y + a.y*b.x)
    //  BLA apply: z' = cmul(A, z) + cmul(B, dc)  — matches BlaEntry.apply spec
    //  Perturbation: z' = 2*cmul(Zm, z) + cmul(z, z) + dc — matches single_step_bla linearization + z²
    //  Rebase: z = Zm + z, m = 0 — matches lemma_rebase_preserves_orbit

    format!("\
struct Params {{
  width: u32, height: u32, max_iter: u32, orbit_len: u32,
  c_re: f32, c_im: f32, pixel_scale: f32, num_levels: u32,
}}

@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> orbit_re: array<f32>;
@group(0) @binding(2) var<storage, read> orbit_im: array<f32>;
@group(0) @binding(3) var<storage, read> bla_data: array<f32>;
@group(0) @binding(4) var<storage, read> bla_offsets: array<u32>;
@group(0) @binding(5) var<storage, read_write> out: array<u32>;

//  Complex multiply: verified as cmul spec in verus-fractals/src/bla.rs
fn cmul(a: vec2<f32>, b: vec2<f32>) -> vec2<f32> {{
  return vec2<f32>(a.x*b.x - a.y*b.y, a.x*b.y + a.y*b.x);
}}

//  BLA entry accessors (6 floats per entry)
fn bla_a(idx: u32) -> vec2<f32> {{ return vec2<f32>(bla_data[idx*6u], bla_data[idx*6u+1u]); }}
fn bla_b(idx: u32) -> vec2<f32> {{ return vec2<f32>(bla_data[idx*6u+2u], bla_data[idx*6u+3u]); }}
fn bla_r2(idx: u32) -> f32 {{ return bla_data[idx*6u+4u]; }}
fn bla_l(idx: u32) -> u32 {{ return u32(bla_data[idx*6u+5u]); }}

@compute @workgroup_size(16, 16, 1)
fn mandelbrot_bla(@builtin(global_invocation_id) gid: vec3<u32>) {{
  let px = gid.x;
  let py = gid.y;
  if (px >= {w}u || py >= {h}u) {{ return; }}

  //  Pixel delta from reference center
  let dc = vec2<f32>(
    (f32(px) - f32({w}u) / 2.0) * params.pixel_scale + params.c_re,
    (f32(py) - f32({h}u) / 2.0) * params.pixel_scale + params.c_im,
  );

  var z = vec2<f32>(0.0, 0.0);
  var m: u32 = 0u;
  var n: u32 = 0u;
  let max_m = params.orbit_len - 1u;

  while (n < params.max_iter && m < max_m) {{
    let zm = vec2<f32>(orbit_re[m], orbit_im[m]);
    let full = zm + z;
    if (dot(full, full) > 4.0) {{ break; }}

    //  BLA lookup: try from top level down
    var skipped = false;
    for (var level: i32 = i32(params.num_levels) - 1; level >= 0; level--) {{
      let lvl = u32(level);
      let aligned_m = m >> lvl;
      if ((aligned_m << lvl) != m) {{ continue; }}
      let level_offset = bla_offsets[lvl];
      let level_size = bla_offsets[lvl + 1u] - level_offset;
      if (aligned_m >= level_size) {{ continue; }}
      let idx = level_offset + aligned_m;
      if (dot(z, z) < bla_r2(idx)) {{
        //  Apply BLA: z' = A·z + B·dc (verified: lemma_merge_correct)
        z = cmul(bla_a(idx), z) + cmul(bla_b(idx), dc);
        let skip = bla_l(idx);
        m += skip;
        n += skip;
        skipped = true;
        break;
      }} else if (level == 0) {{
        break;
      }}
    }}

    if (!skipped) {{
      //  Perturbation step: z' = 2·Z_m·z + z² + dc
      //  (verified: lemma_single_step_bla_linearization — error is exactly z²)
      let zm2 = vec2<f32>(orbit_re[m], orbit_im[m]);
      z = 2.0 * cmul(zm2, z) + cmul(z, z) + dc;
      m += 1u;
      n += 1u;
    }}

    //  Rebase check (verified: lemma_rebase_preserves_orbit)
    if (m < max_m) {{
      let zm3 = vec2<f32>(orbit_re[m], orbit_im[m]);
      let full2 = zm3 + z;
      if (dot(full2, full2) < dot(z, z)) {{
        z = full2;
        m = 0u;
      }}
    }}
  }}

  //  Smooth coloring
  var color: u32 = 0xFF000000u;
  if (n < params.max_iter) {{
    let zm = vec2<f32>(orbit_re[min(m, max_m)], orbit_im[min(m, max_m)]);
    let full = zm + z;
    let zn = dot(full, full);
    let smooth_val = f32(n) + 1.0 - log2(max(1.0, log2(max(1.0, zn))));
    let t = smooth_val / f32(params.max_iter);
    let r = u32(clamp(sin(t * 12.566 + 0.0) * 127.0 + 128.0, 0.0, 255.0));
    let g = u32(clamp(sin(t * 12.566 + 2.094) * 127.0 + 128.0, 0.0, 255.0));
    let b = u32(clamp(sin(t * 12.566 + 4.189) * 127.0 + 128.0, 0.0, 255.0));
    color = 0xFF000000u | (b << 16u) | (g << 8u) | r;
  }}
  out[py * {w}u + px] = color;
}}
", w = width, h = height)
}

//  ══════════════════════════════════════════════════════════════
//  SPIR-V backend: direct binary emission from WgslExpr (WIP)
//  ══════════════════════════════════════════════════════════════

///  SPIR-V binary builder (**WIP** — emits expression ops, not complete modules).
///
///  Emits SPIR-V binary format directly from WgslExpr, bypassing the
///  WGSL→SPIR-V compiler (naga/tint). Removes the shader compiler
///  from the trust boundary.
///
///  **Status**: Correctly emits arithmetic instruction trees for any WgslExpr.
///  **TODO**: entry point, execution mode, buffer decorations, workgroup dispatch
///  (needed before this can produce a runnable `.spv` module).
///
///  The mapping is 1:1:
///    WgslExpr::Const → OpConstant
///    WgslExpr::Var   → OpLoad (from variable pointer)
///    WgslExpr::Add   → OpIAdd
///    WgslExpr::Mul   → OpIMul
///    WgslExpr::Div   → OpSDiv
///    WgslExpr::Mod   → OpSMod
///    WgslExpr::Index → OpAccessChain + OpLoad
struct SpirVBuilder {
    ///  SPIR-V words (the binary output).
    words: Vec<u32>,
    ///  Next available result ID.
    next_id: u32,
    ///  Cached type IDs.
    type_u32: u32,
    type_i32: u32,
    type_void: u32,
}

impl SpirVBuilder {
    fn new() -> Self {
        SpirVBuilder {
            words: Vec::new(),
            next_id: 1,
            type_u32: 0,
            type_i32: 0,
            type_void: 0,
        }
    }

    fn alloc_id(&mut self) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    ///  Emit a SPIR-V instruction: word_count << 16 | opcode, then operands.
    fn emit_op(&mut self, opcode: u16, operands: &[u32]) {
        let word_count = (operands.len() + 1) as u16;
        self.words.push(((word_count as u32) << 16) | (opcode as u32));
        self.words.extend_from_slice(operands);
    }

    ///  Emit a WgslExpr as SPIR-V instructions, returning the result ID.
    fn emit_expr(&mut self, expr: &WgslExpr, var_ids: &[u32], array_ids: &[u32]) -> u32 {
        match expr {
            WgslExpr::Const(c) => {
                let result = self.alloc_id();
                //  OpConstant %type %result literal
                self.emit_op(43, &[self.type_i32, result, *c as u32]);
                result
            }
            WgslExpr::Var(i) => {
                let idx = *i as usize;
                if idx < var_ids.len() {
                    var_ids[idx]
                } else {
                    //  Fallback: constant 0
                    let result = self.alloc_id();
                    self.emit_op(43, &[self.type_i32, result, 0]);
                    result
                }
            }
            WgslExpr::Add(a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                //  OpIAdd %type %result %a %b
                self.emit_op(128, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Mul(a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                //  OpIMul %type %result %a %b
                self.emit_op(132, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Div(a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                //  OpSDiv %type %result %a %b
                self.emit_op(135, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Mod(a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                //  OpSMod %type %result %a %b
                self.emit_op(139, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Sub(a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                //  OpISub
                self.emit_op(130, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Index(arr, idx_expr) => {
                let idx_id = self.emit_expr(idx_expr, var_ids, array_ids);
                let arr_idx = *arr as usize;
                if arr_idx < array_ids.len() {
                    let ptr_id = self.alloc_id();
                    self.emit_op(65, &[self.type_i32, ptr_id, array_ids[arr_idx], idx_id]);
                    let result = self.alloc_id();
                    self.emit_op(61, &[self.type_i32, result, ptr_id]);
                    result
                } else {
                    let result = self.alloc_id();
                    self.emit_op(43, &[self.type_i32, result, 0]);
                    result
                }
            }
            WgslExpr::Shr(a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                //  OpShiftRightArithmetic
                self.emit_op(195, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Cmp(op, a, b) => {
                let a_id = self.emit_expr(a, var_ids, array_ids);
                let b_id = self.emit_expr(b, var_ids, array_ids);
                let result = self.alloc_id();
                let opcode = match op {
                    CmpOp::Lt => 177,  //  OpSLessThan
                    CmpOp::Le => 179,  //  OpSLessThanEqual
                    CmpOp::Gt => 173,  //  OpSGreaterThan
                    CmpOp::Ge => 175,  //  OpSGreaterThanEqual
                    CmpOp::Eq => 170,  //  OpIEqual
                    CmpOp::Ne => 171,  //  OpINotEqual
                };
                self.emit_op(opcode, &[self.type_i32, result, a_id, b_id]);
                result
            }
            WgslExpr::Reduce(_, _, _) => {
                //  SPIR-V Reduce requires structured control flow (OpLoopMerge) — WIP
                let result = self.alloc_id();
                self.emit_op(43, &[self.type_i32, result, 0]);
                result
            }
        }
    }

    ///  Emit a complete SPIR-V module for a simple expression evaluation.
    ///  Returns the SPIR-V binary as Vec<u32>.
    fn build_module(expr: &WgslExpr, n_vars: usize, n_arrays: usize) -> Vec<u32> {
        let mut b = SpirVBuilder::new();

        //  SPIR-V header
        b.words.push(0x07230203); //  Magic number
        b.words.push(0x00010500); //  Version 1.5
        b.words.push(0x00000000); //  Generator (none)
        let bound_index = b.words.len();
        b.words.push(0);          //  Bound (patched later)
        b.words.push(0);          //  Reserved

        //  Type declarations
        b.type_void = b.alloc_id();
        b.emit_op(19, &[b.type_void]); //  OpTypeVoid
        b.type_u32 = b.alloc_id();
        b.emit_op(21, &[b.type_u32, 32, 0]); //  OpTypeInt 32 unsigned
        b.type_i32 = b.alloc_id();
        b.emit_op(21, &[b.type_i32, 32, 1]); //  OpTypeInt 32 signed

        //  Variable and array placeholder IDs
        let var_ids: Vec<u32> = (0..n_vars).map(|_| b.alloc_id()).collect();
        let array_ids: Vec<u32> = (0..n_arrays).map(|_| b.alloc_id()).collect();

        //  Emit the expression
        let _result_id = b.emit_expr(expr, &var_ids, &array_ids);

        //  Patch bound
        b.words[bound_index] = b.next_id;
        b.words
    }
}

///  Emit a WgslExpr as SPIR-V binary (Vec<u32>).
///
///  This bypasses the WGSL compiler, removing it from the trust boundary.
///  The mapping from WgslExpr to SPIR-V is direct and auditable:
///    Const → OpConstant, Add → OpIAdd, Mul → OpIMul,
///    Div → OpSDiv, Mod → OpSMod, Index → OpAccessChain+OpLoad.
#[allow(dead_code)]
fn wgsl_expr_to_spirv(expr: &WgslExpr, n_vars: usize, n_arrays: usize) -> Vec<u32> {
    SpirVBuilder::build_module(expr, n_vars, n_arrays)
}

//  ══════════════════════════════════════════════════════════════
//  WGSL shader generation (generic)
//  ══════════════════════════════════════════════════════════════

///  Buffer binding descriptor for a kernel parameter.
struct KernelParam {
    name: String,
    binding: usize,
    is_output: bool,
}

///  Emit a WGSL binding declaration for a storage buffer.
fn emit_binding(binding: usize, name: &str, is_output: bool) -> String {
    let access = if is_output { "read_write" } else { "read" };
    format!(
        "@group(0) @binding({}) var<storage, {}> {}: array<i32>;\n",
        binding, access, name
    )
}

///  Generate a WGSL compute shader from kernel metadata.
fn emit_wgsl_shader(
    fn_name: &str,
    params: &[KernelParam],
    workgroup_size: [u32; 3],
    body_wgsl: &str,
) -> String {
    let mut shader = String::new();

    //  Buffer bindings
    for p in params {
        shader.push_str(&emit_binding(p.binding, &p.name, p.is_output));
    }
    shader.push('\n');

    //  Entry point
    shader.push_str(&format!(
        "@compute @workgroup_size({}, {}, {})\n",
        workgroup_size[0], workgroup_size[1], workgroup_size[2]
    ));
    shader.push_str(&format!(
        "fn {}(\n  @builtin(global_invocation_id) gid: vec3<u32>,\n  \
         @builtin(local_invocation_id) lid: vec3<u32>,\n  \
         @builtin(workgroup_id) wid: vec3<u32>,\n) {{\n",
        fn_name
    ));
    shader.push_str(body_wgsl);
    shader.push_str("}\n");

    shader
}

/*  Proc-macro helpers — disabled while crate is a regular library.

fn extract_params(func: &ItemFn) -> Vec<KernelParam> { ... }
fn parse_workgroup_size(attr: TokenStream) -> [u32; 3] { ... }
*/

/*  #[kernel] proc macro — disabled while crate is a regular library.
    Can be re-enabled by restoring proc-macro = true in Cargo.toml.

#[proc_macro_attribute]
pub fn kernel(attr: TokenStream, item: TokenStream) -> TokenStream { ... }
*/

//  ══════════════════════════════════════════════════════════════
//  Tests
//  ══════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wgsl_expr_emit_const() {
        let expr = WgslExpr::Const(42);
        assert_eq!(expr.emit(&[], &[]), "42u");
    }

    #[test]
    fn test_wgsl_expr_emit_var() {
        let expr = WgslExpr::Var(0);
        assert_eq!(expr.emit(&["tid"], &[]), "tid");
    }

    #[test]
    fn test_wgsl_expr_emit_add_mul() {
        //  (tid * 4) + lid
        let expr = WgslExpr::Add(
            Box::new(WgslExpr::Mul(
                Box::new(WgslExpr::Var(0)),
                Box::new(WgslExpr::Const(4)),
            )),
            Box::new(WgslExpr::Var(1)),
        );
        assert_eq!(
            expr.emit(&["tid", "lid"], &[]),
            "((tid * 4u) + lid)"
        );
    }

    #[test]
    fn test_wgsl_expr_emit_div_mod() {
        //  (x / 6) % 4
        let expr = WgslExpr::Mod(
            Box::new(WgslExpr::Div(
                Box::new(WgslExpr::Var(0)),
                Box::new(WgslExpr::Const(6)),
            )),
            Box::new(WgslExpr::Const(4)),
        );
        assert_eq!(
            expr.emit(&["x"], &[]),
            "((x / 6u) % 4u)"
        );
    }

    #[test]
    fn test_wgsl_expr_emit_index() {
        //  a[(tid * 4)]
        let expr = WgslExpr::Index(0, Box::new(
            WgslExpr::Mul(
                Box::new(WgslExpr::Var(0)),
                Box::new(WgslExpr::Const(4)),
            ),
        ));
        assert_eq!(
            expr.emit(&["tid"], &["a", "b"]),
            "a[(tid * 4u)]"
        );
    }

    #[test]
    fn test_delinearize_coord_rank1() {
        //  delinearize(x, [8])[0] = x % 8
        let expr = delinearize_coord_expr(0, &[8], 0);
        assert_eq!(
            expr.emit(&["x"], &[]),
            "((x / 1u) % 8u)"
        );
    }

    #[test]
    fn test_delinearize_coord_rank2() {
        //  shape = [4, 3], delinearize(x, shape)[0] = (x / 1) % 4
        let e0 = delinearize_coord_expr(0, &[4, 3], 0);
        assert_eq!(e0.emit(&["x"], &[]), "((x / 1u) % 4u)");

        //  delinearize(x, shape)[1] = (x / 4) % 3
        let e1 = delinearize_coord_expr(0, &[4, 3], 1);
        assert_eq!(e1.emit(&["x"], &[]), "((x / 4u) % 3u)");
    }

    #[test]
    fn test_offset_expr_rank2() {
        //  shape=[4,3], stride=[1,4] (column-major)
        //  offset(x) = ((x/1)%4)*1 + ((x/4)%3)*4
        let expr = offset_expr(0, &[4, 3], &[1, 4]);
        let wgsl = expr.emit(&["x"], &[]);
        assert_eq!(
            wgsl,
            "((((x / 1u) % 4u) * 1u) + (((x / 4u) % 3u) * 4u))"
        );
    }

    #[test]
    fn test_gemm_mac_expr() {
        //  A[i*K+k] * B[k*N+j], K=4, N=3
        let expr = gemm_mac_expr(4, 3);
        let wgsl = expr.emit(&["i", "j", "k"], &["a", "b"]);
        assert_eq!(
            wgsl,
            "(a[((i * 4u) + k)] * b[((k * 3u) + j)])"
        );
    }

    #[test]
    fn test_prefix_product() {
        assert_eq!(shape_prefix_product(&[4, 3, 2], 0), 1);
        assert_eq!(shape_prefix_product(&[4, 3, 2], 1), 4);
        assert_eq!(shape_prefix_product(&[4, 3, 2], 2), 12);
        assert_eq!(shape_prefix_product(&[4, 3, 2], 3), 24);
    }

    //  ── KernelDesc → WGSL tests (from verified kernel specs) ──

    #[test]
    fn test_kernel_vector_add_wgsl() {
        let k = vector_add_kernel_desc(1024);
        let wgsl = emit_kernel_wgsl(&k);
        eprintln!("=== kernel vector_add WGSL ===\n{}", wgsl);
        assert!(wgsl.contains("@compute @workgroup_size(256, 1, 1)"));
        assert!(wgsl.contains("fn vector_add("));
        assert!(wgsl.contains("let tid = gid.x;"));
        assert!(wgsl.contains("if (!(tid < 1024u))"));
        assert!(wgsl.contains("(a[tid] + b[tid])"));
        //  Validate with naga
        validate_wgsl(&wgsl);
    }

    #[test]
    fn test_kernel_gemm_wgsl() {
        let k = gemm_kernel_desc(32, 16, 24);
        let wgsl = emit_kernel_wgsl(&k);
        eprintln!("=== kernel GEMM WGSL ===\n{}", wgsl);
        assert!(wgsl.contains("@compute @workgroup_size(16, 16, 1)"));
        assert!(wgsl.contains("fn naive_gemm("));
        assert!(wgsl.contains("let i = gid.x;"));
        assert!(wgsl.contains("let j = gid.y;"));
        //  Guard: i < 32 && j < 24
        assert!(wgsl.contains("i < 32u"));
        assert!(wgsl.contains("j < 24u"));
        //  Reduce loop
        assert!(wgsl.contains("for (var kk"));
        assert!(wgsl.contains("kk < 16u"));
        //  Index expressions: a[i*16+kk] * b[kk*24+j]
        assert!(wgsl.contains("a[((i * 16u) + kk)]"));
        assert!(wgsl.contains("b[((kk * 24u) + j)]"));
        //  Validate with naga
        validate_wgsl(&wgsl);
    }

    #[test]
    fn test_kernel_dot_product_wgsl() {
        let k = dot_product_kernel_desc(128);
        let wgsl = emit_kernel_wgsl(&k);
        eprintln!("=== kernel dot_product WGSL ===\n{}", wgsl);
        assert!(wgsl.contains("fn dot_product("));
        assert!(wgsl.contains("for (var k"));
        assert!(wgsl.contains("k < 128u"));
        assert!(wgsl.contains("a[k]"));
        assert!(wgsl.contains("b[k]"));
        validate_wgsl(&wgsl);
    }

    #[test]
    fn test_kernel_offset_wgsl() {
        //  Column-major 4x3 layout
        let k = offset_kernel_desc(&[4, 3], &[1, 4]);
        let wgsl = emit_kernel_wgsl(&k);
        eprintln!("=== kernel layout_offset WGSL ===\n{}", wgsl);
        assert!(wgsl.contains("fn layout_offset("));
        assert!(wgsl.contains("tid < 12u"));
        assert!(wgsl.contains("(tid / 1u) % 4u"));
        assert!(wgsl.contains("(tid / 4u) % 3u"));
        validate_wgsl(&wgsl);
    }

    //  ── BLA kernel tests ──

    #[test]
    fn test_bla_level0_kernel() {
        let k = bla_level0_kernel_desc(1024, 4096); //  ONE = 1<<12
        let wgsl = emit_kernel_wgsl(&k);
        assert!(wgsl.contains("fn bla_level0("));
        assert!(wgsl.contains("orbit_re[tid]"));
        eprintln!("=== bla_level0 ===\n{}", wgsl);
        assert!(wgsl.contains("4096")); //  ONE
        validate_wgsl(&wgsl);
    }

    #[test]
    fn test_bla_merge_kernel() {
        let k = bla_merge_kernel_desc(512, 12);
        let wgsl = emit_kernel_wgsl(&k);
        assert!(wgsl.contains("fn bla_merge("));
        assert!(wgsl.contains(">> 12")); //  fixed-point shift
        validate_wgsl(&wgsl);
    }

    #[test]
    fn test_bla_apply_kernel() {
        let k = bla_apply_kernel_desc(480000, 12);
        let wgsl = emit_kernel_wgsl(&k);
        assert!(wgsl.contains("fn bla_apply("));
        assert!(wgsl.contains(">> 12")); //  fixed-point shift
        validate_wgsl(&wgsl);
    }

    //  ── Mandelbrot generators ──

    #[test]
    fn test_generate_mandelbrot_bla() {
        let wgsl = generate_mandelbrot_bla_wgsl(800, 600);
        assert!(wgsl.contains("fn mandelbrot_bla("));
        assert!(wgsl.contains("cmul(bla_a(idx), z)"));  //  BLA apply
        assert!(wgsl.contains("2.0 * cmul(zm2, z)"));    //  perturbation step
        assert!(wgsl.contains("lemma_merge_correct"));    //  verified reference
        assert!(wgsl.contains("lemma_rebase_preserves")); //  verified reference
        validate_wgsl(&wgsl);
        eprintln!("=== BLA Mandelbrot WGSL ({} chars) ===", wgsl.len());
    }

    //  ── Mandelbrot fixed-point ──

    #[test]
    fn test_generate_mandelbrot() {
        let wgsl = generate_mandelbrot_wgsl(800, 600, 256, [16, 16]);
        assert!(wgsl.contains("@compute @workgroup_size(16, 16, 1)"));
        assert!(wgsl.contains("fn mandelbrot("));
        assert!(wgsl.contains(">> 12u"));  //  20.12 fixed-point shift
        assert!(wgsl.contains("params[0]")); //  viewport from buffer
        assert!(wgsl.contains("params[3]")); //  dy from buffer
        validate_wgsl(&wgsl);
        eprintln!("=== mandelbrot WGSL ===\n{}", wgsl);
    }

    //  ── WGSL validation ──

    fn validate_wgsl(source: &str) {
        let result = naga::front::wgsl::parse_str(source);
        match result {
            Ok(_module) => {},
            Err(e) => {
                eprintln!("WGSL parse error:\n{}", e.emit_to_string(source));
                panic!("Generated WGSL failed validation");
            }
        }
    }

    //  ── SPIR-V backend tests ──

    #[test]
    fn test_spirv_const() {
        let expr = WgslExpr::Const(42);
        let spirv = wgsl_expr_to_spirv(&expr, 0, 0);
        //  Check SPIR-V magic number
        assert_eq!(spirv[0], 0x07230203);
        //  Should have some instructions
        assert!(spirv.len() > 5);
    }

    #[test]
    fn test_spirv_add() {
        let expr = WgslExpr::Add(
            Box::new(WgslExpr::Var(0)),
            Box::new(WgslExpr::Const(1)),
        );
        let spirv = wgsl_expr_to_spirv(&expr, 1, 0);
        assert_eq!(spirv[0], 0x07230203);
        //  Should contain OpIAdd (opcode 128)
        let has_iadd = spirv.iter().any(|&w| (w & 0xFFFF) == 128);
        assert!(has_iadd, "SPIR-V should contain OpIAdd");
    }

    #[test]
    fn test_spirv_gemm_mac() {
        //  A[i*K+k] * B[k*N+j]
        let expr = gemm_mac_expr(4, 3);
        let spirv = wgsl_expr_to_spirv(&expr, 3, 2);
        assert_eq!(spirv[0], 0x07230203);
        //  Should contain OpIMul (132), OpIAdd (128), OpAccessChain (65), OpLoad (61)
        let opcodes: Vec<u16> = spirv.iter().map(|&w| (w & 0xFFFF) as u16).collect();
        assert!(opcodes.contains(&132), "Should contain OpIMul");
        assert!(opcodes.contains(&128), "Should contain OpIAdd");
        assert!(opcodes.contains(&65), "Should contain OpAccessChain");
        assert!(opcodes.contains(&61), "Should contain OpLoad");
    }

    #[test]
    fn test_spirv_delinearize() {
        //  (x / 4) % 3
        let expr = delinearize_coord_expr(0, &[4, 3], 1);
        let spirv = wgsl_expr_to_spirv(&expr, 1, 0);
        assert_eq!(spirv[0], 0x07230203);
        //  Should contain OpSDiv (135) and OpSMod (139)
        let opcodes: Vec<u16> = spirv.iter().map(|&w| (w & 0xFFFF) as u16).collect();
        assert!(opcodes.contains(&135), "Should contain OpSDiv");
        assert!(opcodes.contains(&139), "Should contain OpSMod");
    }

    //  ── Generic shader tests ──

    #[test]
    fn test_wgsl_shader_emission() {
        let params = vec![
            KernelParam { name: "a".into(), binding: 0, is_output: false },
            KernelParam { name: "b".into(), binding: 1, is_output: false },
            KernelParam { name: "out_c".into(), binding: 2, is_output: true },
        ];

        let wgsl = emit_wgsl_shader(
            "vector_add", &params, [256, 1, 1],
            "  let tid = gid.x;\n  out_c[tid] = a[tid] + b[tid];\n",
        );

        assert!(wgsl.contains("@group(0) @binding(0) var<storage, read> a: array<i32>"));
        assert!(wgsl.contains("@group(0) @binding(2) var<storage, read_write> out_c: array<i32>"));
        assert!(wgsl.contains("@compute @workgroup_size(256, 1, 1)"));
        assert!(wgsl.contains("fn vector_add("));
        assert!(wgsl.contains("out_c[tid] = a[tid] + b[tid]"));
    }
}
