import Qcircuits.Strategies

open Matrix Complex DiracRepr

noncomputable section

namespace DiracRepr

/-! ### Density matrix -/

/-- The density matrix of a pure state |ψ⟩ is ρ = |ψ⟩⟨ψ|. -/
def density {n : ℕ} (ψ : Matrix (Fin n) (Fin 1) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ψ * ψᴴ


/-! ### Super operator -/

/-- The super operator: super M ρ = M × ρ × M†.
    This represents the action of a unitary gate M on a density matrix ρ. -/
def super {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  M * ρ * Mᴴ


/-! ### Basic properties of density matrices -/

/-- The density matrix is Hermitian: (density ψ)ᴴ = density ψ -/
theorem density_conjTranspose {n : ℕ} (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    (density ψ)ᴴ = density ψ := by
  unfold density
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-
Super operator preserves Hermiticity:
    If ρ is Hermitian, then super M ρ is Hermitian.
-/
theorem super_conjTranspose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρᴴ = ρ) :
    (super M ρ)ᴴ = super M ρ := by
  unfold super; simp +decide [ hρ, Matrix.mul_assoc ] ;

/-
super operator is compatible with density:
    super M (density ψ) = density (M × ψ)
-/
theorem super_density {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (ψ : Matrix (Fin n) (Fin 1) ℂ) :
    super M (density ψ) = density (M * ψ) := by
  unfold super density;
  simp +decide [ Matrix.mul_assoc ]

end DiracRepr
end
