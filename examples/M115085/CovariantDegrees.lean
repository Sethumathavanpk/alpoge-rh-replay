import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup

namespace UpperTheory.Reformulated.B.CovariantDegrees

noncomputable def jE
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : Field Ω] :
    [Algebra E Ω] → (Ω →+* PadicAlgCl l) → E →+* PadicAlgCl l :=
  fun [_] j => j.comp (algebraMap E Ω)

theorem aux2 {E : Type} [Field E] [inst_1 : NumberField E] : Module.Free ℚ E :=
  Module.Free.of_divisionRing ℚ E

attribute [local instance 10000] aux2

noncomputable def KwF
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [NumberField E]
    [inst_2 : Field Ω] : [Algebra E Ω] → (Ω →+* PadicAlgCl l) →
    IntermediateField ℚ_[l] (PadicAlgCl l) :=
  fun [_] j => IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE j (Module.finBasis ℚ E i))

@[reducible] noncomputable def G.{u_1, u_2}
    (F : Type u_1) (Ω : Type u_2) [Field F] [inst_1 : Field Ω] : [Algebra F Ω] → Type u_2 :=
  fun [_] => Ω ≃ₐ[F] Ω

noncomputable def Dec.{u_1, u_2}
    {F : Type u_1} {Ω : Type u_2} [Field F] [inst_1 : Field Ω] [inst_2 : Algebra F Ω] :
    ValuationSubring Ω → Subgroup (G F Ω) :=
  fun A => ValuationSubring.decompositionSubgroup F A

theorem aux6 {E Ω : Type} [Field E] [inst_1 : Field Ω] [inst_2 : Algebra E Ω] :
    Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree

theorem aux7 {Ω : Type} [Field Ω] [inst_1 : CharZero Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance 10000] aux6 aux7

@[reducible] noncomputable def Om (l : Nat) [Fact (Nat.Prime l)] : Type := PadicAlgCl l

@[reducible] noncomputable def GQ (l : Nat) [Fact (Nat.Prime l)] : Type :=
  Om l ≃ₐ[ℚ_[l]] Om l

theorem laurent_T_neg_one_mul_T_one {l : Nat} [hl : Fact (Nat.Prime l)] :
    IsScalarTower ℚ ℚ_[l] (Om l) := inferInstance

attribute [local instance 10000] laurent_T_neg_one_mul_T_one

theorem aux11 {l : Nat} [hl : Fact (Nat.Prime l)] {Ω : Type} [Field Ω] [inst_1 : CharZero Ω]
    (j : Ω →+* PadicAlgCl l) :
    @IsScalarTower ℚ Ω (PadicAlgCl l) _ j.toAlgebra.toSMul _ :=
  let _ := j.toAlgebra; IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem aux12 {Ω : Type} [Field Ω] [inst_1 : CharZero Ω] : [IsAlgClosure ℚ Ω] → Normal ℚ Ω :=
  fun [_] => IsAlgClosure.normal ℚ Ω

attribute [local instance 10000] aux12

noncomputable def resQ
    {l : Nat} [hl : Fact (Nat.Prime l)] {Ω : Type} [Field Ω] [inst_1 : CharZero Ω] :
    [IsAlgClosure ℚ Ω] → (Ω →+* PadicAlgCl l) → GQ l → Ω ≃ₐ[ℚ] Ω :=
  fun [_] j σ =>
    letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
    haveI := aux11 j
    (σ.restrictScalars ℚ).toAlgHom.restrictNormal' Ω

private theorem j_resQ {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l) (σ : GQ l) (x : Ω) :
    j (resQ j σ x) = σ (j x) :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI := aux11 j
  AlgHom.restrictNormal_commutes (σ.restrictScalars ℚ).toAlgHom Ω x

theorem zero_contDiffOn_supported
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : CharZero Ω] [inst_5 : IsAlgClosure ℚ Ω]
    (j : Ω →+* PadicAlgCl l) (σ : GQ l) :
    σ ∈ (KwF (E := E) j).fixingSubgroup →
    ∀ (x : E), resQ j σ (algebraMap E Ω x) = algebraMap E Ω x := by
  intro hσ x
  apply j.injective
  refine (j_resQ j σ _).trans ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ (jE j x) ?_)
  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

noncomputable def resE
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : CharZero Ω] :
    [IsAlgClosure ℚ Ω] → (j : Ω →+* PadicAlgCl l) → (σ : GQ l) →
    σ ∈ (KwF (E := E) j).fixingSubgroup → G E Ω :=
  fun [_] j σ hσ =>
    AlgEquiv.ofRingEquiv (f := (resQ j σ).toRingEquiv) (zero_contDiffOn_supported (E := E) j σ hσ)

theorem column_matrix_mul_inverse
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] {j : Ω →+* PadicAlgCl l}
    (σ : (KwF (E := E) j).fixingSubgroup) :
    (σ : GQ l) ∈ (KwF (E := E) j).fixingSubgroup := σ.2

open Pointwise in
theorem complex_normed_instance_compat
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] [inst_5 : CharZero Ω]
    [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} :
    (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (σ : (KwF (E := E) j).fixingSubgroup),
    resE j σ.1 (column_matrix_mul_inverse σ) ∈ Dec (F := E) A := by
  intro hj σ
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hj, hj]
  have hn : ‖j ((resE j σ.1 σ.2)⁻¹ • x)‖ = ‖j x‖ := by
    change ‖j ((resE j σ.1 σ.2).symm x)‖ = ‖j x‖
    have hx := j_resQ j σ.1 ((resE j σ.1 σ.2).symm x)
    have heq : resQ j σ.1 ((resE j σ.1 σ.2).symm x) = x := (resE j σ.1 σ.2).apply_symm_apply x
    rw [heq] at hx
    rw [hx]
    exact spectralNorm_eq_of_equiv σ.1 _
  rw [hn]

theorem padic_embedding_algebra_compat
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] {j : Ω →+* PadicAlgCl l} :
    ((1 : (KwF (E := E) j).fixingSubgroup) : GQ l) ∈ (KwF (E := E) j).fixingSubgroup :=
  Subgroup.one_mem _

theorem blockM_one_partner_eq_one
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] [inst_5 : CharZero Ω]
    [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} :
    (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
    resE j (1 : (KwF (E := E) j).fixingSubgroup).1 padic_embedding_algebra_compat ∈
      Dec (F := E) A :=
  fun hj => complex_normed_instance_compat (E := E) hj 1

theorem blockM_mul_alt
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω]
    [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
    (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) :
    (⟨resE j (1 : (KwF (E := E) j).fixingSubgroup).1 padic_embedding_algebra_compat,
      blockM_one_partner_eq_one hj⟩ : Dec (F := E) A) = 1 :=
  Subtype.ext (AlgEquiv.ext fun x => j.injective (j_resQ j 1 x))

theorem conj_invariant_character_mem
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] {j : Ω →+* PadicAlgCl l}
    (σ τ : (KwF (E := E) j).fixingSubgroup) :
    ((σ * τ : (KwF (E := E) j).fixingSubgroup) : GQ l) ∈ (KwF (E := E) j).fixingSubgroup :=
  (σ * τ).2

theorem rootGL_mem_unitary
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] [inst_5 : CharZero Ω]
    [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} :
    (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (σ τ : (KwF (E := E) j).fixingSubgroup),
    resE j (σ * τ).1 (conj_invariant_character_mem σ τ) ∈ Dec (F := E) A :=
  fun hj σ τ => complex_normed_instance_compat (E := E) hj (σ * τ)

theorem conj_invariant_character_transport
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω]
    [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
    (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) (σ τ : (KwF (E := E) j).fixingSubgroup) :
    (⟨resE j (σ * τ).1 (conj_invariant_character_mem σ τ), rootGL_mem_unitary hj σ τ⟩ :
      Dec (F := E) A) =
      ⟨resE j σ.1 (column_matrix_mul_inverse σ), complex_normed_instance_compat hj σ⟩ *
      ⟨resE j τ.1 (column_matrix_mul_inverse τ), complex_normed_instance_compat hj τ⟩ := by
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  exact (j_resQ j (σ * τ).1 x).trans
    ((j_resQ j σ.1 (resE j τ.1 τ.2 x)).trans (congrArg σ.1 (j_resQ j τ.1 x))).symm

noncomputable def rHom
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] [inst_5 : CharZero Ω] :
    [IsAlgClosure ℚ Ω] → {j : Ω →+* PadicAlgCl l} → {A : ValuationSubring Ω} →
    (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
    (KwF (E := E) j).fixingSubgroup →* Dec (F := E) A :=
  fun [_] {j _} hj =>
    { toFun := fun σ => ⟨resE j σ.1 (column_matrix_mul_inverse σ),
        complex_normed_instance_compat (E := E) hj σ⟩
      map_one' := blockM_mul_alt (E := E) hj
      map_mul' := conj_invariant_character_transport (E := E) hj }

theorem continuous_rHom
    {l : Nat} [hl : Fact (Nat.Prime l)] {E Ω : Type} [Field E] [inst_1 : NumberField E]
    [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω]
    [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
    (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) :
    Continuous (rHom (E := E) (A := A) hj) := by
  refine continuous_induced_rng.2
    (continuous_of_continuousAt_one ((Dec (F := E) A).subtype.comp (rHom (E := E) hj)) ?_)
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨L, _, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
  let b := Module.finBasis E L
  have hU : ∀ᶠ σ : (KwF (E := E) j).fixingSubgroup in nhds 1, ∀ i, σ.1 (j (b i)) = j (b i) :=
    Filter.eventually_all.2 fun i =>
      ((stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        continuous_subtype_val).mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
  refine hU.mono fun σ hσ => hLs ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_)
  have key : (resE j σ.1 σ.2).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => j.injective ((j_resQ j σ.1 (b i)).trans (hσ i))
  exact LinearMap.congr_fun key ⟨x, hx⟩

end UpperTheory.Reformulated.B.CovariantDegrees
