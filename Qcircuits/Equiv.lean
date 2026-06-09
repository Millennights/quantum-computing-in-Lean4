import Qcircuits.Density

open Matrix Complex DiracRepr

noncomputable section

namespace DiracRepr

/-! ### Matrix equivalence characterized by action on vectors -/

/-
Two matrices are equal iff they act identically on all column vectors.
    A = B ↔ ∀ v, A × v = B × v
-/
theorem MatrixEquiv_spec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    A = B ↔ (∀ v : Matrix (Fin n) (Fin 1) ℂ, A * v = B * v) := by
  refine' ⟨ fun h => by simp +decide [ h ], fun h => _ ⟩;
  ext i j;
  convert congr_fun ( congr_fun ( h ( Matrix.of fun k l => if k = j then 1 else 0 ) ) i ) 0 using 1 <;> simp +decide [ Matrix.mul_apply ]

/-
If two matrices act identically on all vectors, they are equal.
    This is the non-trivial direction of MatrixEquiv_spec.
-/
theorem mat_equiv_by_Mmult {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℂ)
    (h : ∀ v : Matrix (Fin n) (Fin 1) ℂ, A * v = B * v) :
    A = B := by
  ext i j;
  convert congr_arg ( fun v : Matrix ( Fin m ) ( Fin 1 ) ℂ => v i 0 ) ( h ( Matrix.of fun x y => if x = j then 1 else 0 ) ) using 1 <;> simp +decide [ Matrix.mul_apply ]


/-! ### Useful corollaries -/

/-
The identity matrix is the unique matrix satisfying I × v = v for all v.
-/
theorem identity_unique {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v : Matrix (Fin n) (Fin 1) ℂ, A * v = v) :
    A = 1 := by
  convert mat_equiv_by_Mmult A 1 _;
  aesop


/-! ### Properties relating matrix equivalence and density matrices -/

/-- If A = B as matrices, then they produce the same density matrix from any state. -/
theorem density_eq_of_matrix_eq {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℂ) (ψ : Matrix (Fin n) (Fin 1) ℂ)
    (h : A = B) :
    density (A * ψ) = density (B * ψ) := by
  rw [h]

/-- If A = B, then super A ρ = super B ρ for any density matrix ρ. -/
theorem super_eq_of_matrix_eq {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (h : A = B) :
    super A ρ = super B ρ := by
  rw [h]

end DiracRepr
end
