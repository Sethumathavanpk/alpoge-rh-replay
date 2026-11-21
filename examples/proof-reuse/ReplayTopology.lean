import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix

namespace ReplayTopology

/-- A group homomorphism into the units is continuous if its values are continuous in the monoid. -/
theorem continuous_unitsHom {G R : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
    [Monoid R] [TopologicalSpace R] (f : G →* Rˣ) (h : Continuous fun x => (f x : R)) :
    Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

/-- Quotienting a compact totally disconnected group by a closed normal subgroup preserves
total disconnectedness. The image of an open subgroup separates each nonidentity coset from 1. -/
theorem totallyDisconnected_quotient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) : TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

/-- Each coefficient of the characteristic polynomial of an `ι × ι` matrix over a topological
commutative ring depends continuously on the matrix entries. -/
theorem continuous_charpoly_coeff {K ι : Type*} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [Fintype ι] [DecidableEq ι] (i : ℕ) :
    Continuous fun M : Matrix ι ι K => M.charpoly.coeff i := by
  have h : (fun M : Matrix ι ι K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : ι × ι => M ij.1 ij.2)
        ((Matrix.charpoly.univ K ι).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom ι (RingHom.id K)
      (fun ij : ι × ι => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end ReplayTopology
