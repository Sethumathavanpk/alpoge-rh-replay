import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
import PublishedCovariantDegrees
import Lean.Util.CollectAxioms

universe v1 v2

example : @PublishedCovariantDegrees.jE = @UpperTheory.Reformulated.B.CovariantDegrees.jE := rfl
example : @PublishedCovariantDegrees.aux2 = @UpperTheory.Reformulated.B.CovariantDegrees.aux2 := rfl
example : @PublishedCovariantDegrees.KwF = @UpperTheory.Reformulated.B.CovariantDegrees.KwF := rfl
example : @PublishedCovariantDegrees.G.{v1, v2} = @UpperTheory.Reformulated.B.CovariantDegrees.G.{v1, v2} := rfl
example : @PublishedCovariantDegrees.Dec.{v1, v2} = @UpperTheory.Reformulated.B.CovariantDegrees.Dec.{v1, v2} := rfl
example : @PublishedCovariantDegrees.aux6 = @UpperTheory.Reformulated.B.CovariantDegrees.aux6 := rfl
example : @PublishedCovariantDegrees.aux7 = @UpperTheory.Reformulated.B.CovariantDegrees.aux7 := rfl
example : @PublishedCovariantDegrees.Om = @UpperTheory.Reformulated.B.CovariantDegrees.Om := rfl
example : @PublishedCovariantDegrees.GQ = @UpperTheory.Reformulated.B.CovariantDegrees.GQ := rfl
example : @PublishedCovariantDegrees.laurent_T_neg_one_mul_T_one = @UpperTheory.Reformulated.B.CovariantDegrees.laurent_T_neg_one_mul_T_one := rfl
example : @PublishedCovariantDegrees.aux11 = @UpperTheory.Reformulated.B.CovariantDegrees.aux11 := rfl
example : @PublishedCovariantDegrees.aux12 = @UpperTheory.Reformulated.B.CovariantDegrees.aux12 := rfl
example : @PublishedCovariantDegrees.resQ = @UpperTheory.Reformulated.B.CovariantDegrees.resQ := rfl
example : @PublishedCovariantDegrees.zero_contDiffOn_supported = @UpperTheory.Reformulated.B.CovariantDegrees.zero_contDiffOn_supported := rfl
example : @PublishedCovariantDegrees.resE = @UpperTheory.Reformulated.B.CovariantDegrees.resE := rfl
example : @PublishedCovariantDegrees.column_matrix_mul_inverse = @UpperTheory.Reformulated.B.CovariantDegrees.column_matrix_mul_inverse := rfl
example : @PublishedCovariantDegrees.complex_normed_instance_compat = @UpperTheory.Reformulated.B.CovariantDegrees.complex_normed_instance_compat := rfl
example : @PublishedCovariantDegrees.padic_embedding_algebra_compat = @UpperTheory.Reformulated.B.CovariantDegrees.padic_embedding_algebra_compat := rfl
example : @PublishedCovariantDegrees.blockM_one_partner_eq_one = @UpperTheory.Reformulated.B.CovariantDegrees.blockM_one_partner_eq_one := rfl
example : @PublishedCovariantDegrees.blockM_mul_alt = @UpperTheory.Reformulated.B.CovariantDegrees.blockM_mul_alt := rfl
example : @PublishedCovariantDegrees.conj_invariant_character_mem = @UpperTheory.Reformulated.B.CovariantDegrees.conj_invariant_character_mem := rfl
example : @PublishedCovariantDegrees.rootGL_mem_unitary = @UpperTheory.Reformulated.B.CovariantDegrees.rootGL_mem_unitary := rfl
example : @PublishedCovariantDegrees.conj_invariant_character_transport = @UpperTheory.Reformulated.B.CovariantDegrees.conj_invariant_character_transport := rfl
example : @PublishedCovariantDegrees.rHom = @UpperTheory.Reformulated.B.CovariantDegrees.rHom := rfl
example : @PublishedCovariantDegrees.continuous_rHom = @UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom := rfl

open Lean Elab Command in
run_cmd
  let env ← getEnv
  let rec binders : Expr → List (Name × BinderInfo)
    | .forallE n _ body bi => (n.eraseMacroScopes, bi) :: binders body
    | _ => []
  let pairs := [
    (``PublishedCovariantDegrees.jE, ``UpperTheory.Reformulated.B.CovariantDegrees.jE),
    (``PublishedCovariantDegrees.aux2, ``UpperTheory.Reformulated.B.CovariantDegrees.aux2),
    (``PublishedCovariantDegrees.KwF, ``UpperTheory.Reformulated.B.CovariantDegrees.KwF),
    (``PublishedCovariantDegrees.G, ``UpperTheory.Reformulated.B.CovariantDegrees.G),
    (``PublishedCovariantDegrees.Dec, ``UpperTheory.Reformulated.B.CovariantDegrees.Dec),
    (``PublishedCovariantDegrees.aux6, ``UpperTheory.Reformulated.B.CovariantDegrees.aux6),
    (``PublishedCovariantDegrees.aux7, ``UpperTheory.Reformulated.B.CovariantDegrees.aux7),
    (``PublishedCovariantDegrees.Om, ``UpperTheory.Reformulated.B.CovariantDegrees.Om),
    (``PublishedCovariantDegrees.GQ, ``UpperTheory.Reformulated.B.CovariantDegrees.GQ),
    (``PublishedCovariantDegrees.laurent_T_neg_one_mul_T_one, ``UpperTheory.Reformulated.B.CovariantDegrees.laurent_T_neg_one_mul_T_one),
    (``PublishedCovariantDegrees.aux11, ``UpperTheory.Reformulated.B.CovariantDegrees.aux11),
    (``PublishedCovariantDegrees.aux12, ``UpperTheory.Reformulated.B.CovariantDegrees.aux12),
    (``PublishedCovariantDegrees.resQ, ``UpperTheory.Reformulated.B.CovariantDegrees.resQ),
    (``PublishedCovariantDegrees.zero_contDiffOn_supported, ``UpperTheory.Reformulated.B.CovariantDegrees.zero_contDiffOn_supported),
    (``PublishedCovariantDegrees.resE, ``UpperTheory.Reformulated.B.CovariantDegrees.resE),
    (``PublishedCovariantDegrees.column_matrix_mul_inverse, ``UpperTheory.Reformulated.B.CovariantDegrees.column_matrix_mul_inverse),
    (``PublishedCovariantDegrees.complex_normed_instance_compat, ``UpperTheory.Reformulated.B.CovariantDegrees.complex_normed_instance_compat),
    (``PublishedCovariantDegrees.padic_embedding_algebra_compat, ``UpperTheory.Reformulated.B.CovariantDegrees.padic_embedding_algebra_compat),
    (``PublishedCovariantDegrees.blockM_one_partner_eq_one, ``UpperTheory.Reformulated.B.CovariantDegrees.blockM_one_partner_eq_one),
    (``PublishedCovariantDegrees.blockM_mul_alt, ``UpperTheory.Reformulated.B.CovariantDegrees.blockM_mul_alt),
    (``PublishedCovariantDegrees.conj_invariant_character_mem, ``UpperTheory.Reformulated.B.CovariantDegrees.conj_invariant_character_mem),
    (``PublishedCovariantDegrees.rootGL_mem_unitary, ``UpperTheory.Reformulated.B.CovariantDegrees.rootGL_mem_unitary),
    (``PublishedCovariantDegrees.conj_invariant_character_transport, ``UpperTheory.Reformulated.B.CovariantDegrees.conj_invariant_character_transport),
    (``PublishedCovariantDegrees.rHom, ``UpperTheory.Reformulated.B.CovariantDegrees.rHom),
    (``PublishedCovariantDegrees.continuous_rHom, ``UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom)]
  let some idx := env.getModuleIdx? `PublishedCovariantDegrees | throwError "missing PublishedCovariantDegrees"
  let covered := pairs.map Prod.fst
  for n in env.header.moduleData[idx]!.constNames do
    if !n.isInternalDetail && !isPrivateName n && n.getString! != "congr_simp" then
      unless covered.contains n do
        throwError "published public declaration omitted from audit: {n}"
  let mut mismatches : Nat := 0
  for (p, q) in pairs do
    let some a := env.find? p | throwError "original missing: {p}"
    let some b := env.find? q | throwError "replacement missing: {q}"
    unless a.levelParams == b.levelParams && binders a.type == binders b.type do
      mismatches := mismatches + 1
      logInfo m!"public parameters differ for {q}: {a.levelParams}, {repr (binders a.type)} vs {b.levelParams}, {repr (binders b.type)}"
  if mismatches > 0 then throwError "{mismatches} public parameter mismatches"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (_, q) in pairs do
    for ax in ← collectAxioms q do
      unless allowed.contains ax do
        throwError "unexpected axiom {ax} in {q}"
  logInfo m!"Matched public binder names, visibility and universes for {pairs.length} declarations"
  logInfo m!"Verified standard axioms only ([propext, Classical.choice, Quot.sound]) across all {pairs.length} public declarations"

#print axioms UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom
