import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

open AlgebraicGeometry CategoryTheory IsDedekindDomain NumberField Polynomial
open scoped Padic

namespace ReplayAlgebra

universe u

/-- Contravariant functoriality of `Spec.map` on ring homomorphisms packaged via `CommRingCat.ofHom`. -/
theorem specMap_ofHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]; rfl

/-- In an extension of number fields `K'/K`, the residue-field cardinality of a prime `w` of `𝓞 K'`
equals that of `w.under (𝓞 K)` raised to the inertia degree. -/
theorem cardQuot_under_eq_pow_inertiaDeg (K : Type*) {K' : Type*} [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra K K'] (w : HeightOneSpectrum (𝓞 K')) :
    Nat.card (𝓞 K' ⧸ w.asIdeal) =
      Nat.card (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal =
    Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

/-- No number field is simultaneously totally real and totally complex. -/
theorem not_isTotallyReal_and_isTotallyComplex {F : Type*} [Field F] [NumberField F]
    (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

/-- An element of `PadicAlgCl l` is integral over `ℤ_[l]` if and only if its norm is at most `1`. -/
theorem padicAlgCl_isIntegral_iff_norm_le_one {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) :
    IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/-- Any algebra homomorphism out of a local `O`-algebra into a nontrivial integral `O`-algebra is local. -/
theorem isLocalHom_of_isIntegral {O R A : Type*} [CommRing O] [CommRing R] [IsLocalRing R]
    [Algebra O R] [CommRing A] [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A]
    (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  have : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

end ReplayAlgebra
