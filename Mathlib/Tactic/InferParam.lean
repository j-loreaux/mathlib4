/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Lean
import Mathlib.Lean.Expr.Basic

/-!
# Infer an optional parameter

In this file we define a tactic `infer_opt_param` that closes a goal with default value by using
this default value.

## TODO

Add `infer_auto_param`
-/

namespace Mathlib.Tactic

open Lean Elab Tactic Meta

/-- Close a goal of the form `optParam α a` by using `a`. -/
elab (name := inferOptParam) "infer_opt_param" : tactic => do
  withMainContext do
    let tgt_expr ← getMainTarget
    let goal ← getMainGoal
    match tgt_expr.getAppFnArgs with
    | (``optParam, #[_ty, val]) => assignExprMVar goal val; replaceMainGoal []
    | _ => throwError "`infer_opt_param` only solves goals of the form `optParam _ _`, not {tgt_expr}"
