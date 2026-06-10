import Qcircuits.Strategies

open Matrix Complex DiracRepr

noncomputable section

namespace DiracRepr

/-! ## Multi-qubit states -/

/-- |00⟩ = |0⟩ ⊗ |0⟩ -/
def ket00 : Matrix (Fin 4) (Fin 1) ℂ := ket0 ⊗ ket0

/-- |01⟩ = |0⟩ ⊗ |1⟩ -/
def ket01 : Matrix (Fin 4) (Fin 1) ℂ := ket0 ⊗ ket1

/-- |10⟩ = |1⟩ ⊗ |0⟩ -/
def ket10 : Matrix (Fin 4) (Fin 1) ℂ := ket1 ⊗ ket0

/-- |11⟩ = |1⟩ ⊗ |1⟩ -/
def ket11 : Matrix (Fin 4) (Fin 1) ℂ := ket1 ⊗ ket1

/-- |000⟩ = |0⟩ ⊗ |0⟩ ⊗ |0⟩ -/
def ket000 : Matrix (Fin 8) (Fin 1) ℂ := ket0 ⊗ (ket0 ⊗ ket0)

/-- |111⟩ = |1⟩ ⊗ |1⟩ ⊗ |1⟩ -/
def ket111 : Matrix (Fin 8) (Fin 1) ℂ := ket1 ⊗ (ket1 ⊗ ket1)


/-! ## CX gate action on 2-qubit basis states -/

theorem CX_ket00 : CX * ket00 = ket00 := by
  ext i j;
  fin_cases i <;> fin_cases j <;> simp +decide [ CX, ket00, Matrix.mul_apply ];
  · unfold B0 B3 X_gate; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, Matrix.add_mul, Matrix.mul_add ] ;
    simp +decide [kron];
    simp +decide [ Fin.divNat, Fin.modNat, I₂ ];
  · simp +decide [ B0, B3, X_gate, I₂, kron ];
    simp +decide [ Fin.sum_univ_succ, Fin.modNat, Fin.divNat ];
  · simp +decide [ B0, B3, X_gate, I₂, kron ];
    simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat ];
  · simp +decide [ B0, B3, X_gate, I₂, kron ];
    simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat ]

theorem CX_ket01 : CX * ket01 = ket01 := by
  unfold CX ket01;
  ext i j; simp +decide [*, Matrix.mul_apply] ;
  fin_cases i <;> fin_cases j <;> simp +decide [ B0, B3, I₂, X_gate, kron ];
  · simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat ];
  · simp +decide [ Fin.sum_univ_succ, Matrix.one_apply ];
    simp +decide [ Fin.divNat, Fin.modNat ];
  · simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat ];
  · simp +decide [ Fin.sum_univ_succ, Fin.divNat, Fin.modNat ]

theorem CX_ket10 : CX * ket10 = ket11 := by
  unfold CX ket10 ket11 B0 X_gate;
  simp +decide [B1, B2, B3, ket0, bra0, ket1, bra1, I₂];
  ext i j;
  simp +decide [ Fin.sum_univ_succ, Matrix.mul_apply, kron ];
  fin_cases i <;> simp +decide [ Fin.divNat, Fin.modNat ]

theorem CX_ket11 : CX * ket11 = ket10 := by
  unfold CX ket11 ket10;
  ext i j;
  fin_cases i <;> fin_cases j <;> simp +decide [Matrix.mul_apply, Matrix.add_apply,
    Fin.sum_univ_succ];
  · simp +decide [ B0, B3, X_gate, kron ];
    simp +decide [ Fin.divNat, Fin.modNat ];
  · simp +decide [ B0, B3, X_gate, kron ];
    simp +decide [ Fin.divNat, Fin.modNat, B1, B2, I₂ ];
  · unfold B0 B3 X_gate; norm_num [ Matrix.mul_apply, kron ] ;
    unfold B1 B2; norm_num [ Fin.divNat, Fin.modNat ] ;
  · simp +decide [ B0, B3, X_gate, kron ];
    simp +decide [ Fin.divNat, Fin.modNat, I₂, B1, B2 ]


/-! ## Step-by-step GHZ circuit computation

The GHZ circuit applies three layers to |000⟩:
  Layer 1: (H ⊗ I₂ ⊗ I₂) × |000⟩ = |+⟩ ⊗ |00⟩
  Layer 2: (CX ⊗ I₂) × (|+⟩ ⊗ |00⟩) = (1/√2)|000⟩ + (1/√2)|110⟩
  Layer 3: (I₂ ⊗ CX) × result = (1/√2)|000⟩ + (1/√2)|111⟩
-/

/-
Layer 1: (H ⊗ I₂ ⊗ I₂) × |000⟩ = |+⟩ ⊗ (|0⟩ ⊗ |0⟩)
    Using L13 (mixed product property), this reduces to (H|0⟩) ⊗ (I₂|0⟩ ⊗ I₂|0⟩) = |+⟩ ⊗ |00⟩
-/
theorem ghz_layer1 :
    (H_gate ⊗ (I₂ ⊗ I₂)) * ket000 = ket_plus ⊗ (ket0 ⊗ ket0) := by
      -- Apply the mixed product property of the tensor product.
      have h_mixed : (H_gate ⊗ (I₂ ⊗ I₂)) * (ket0 ⊗ (ket0 ⊗ ket0)) = (H_gate * ket0) ⊗ ((I₂ ⊗ I₂) * (ket0 ⊗ ket0)) := by
        convert L13_kron_mul_kron _ _ _ _ using 1;
      -- By definition of matrix multiplication, we can expand the product.
      have h_expand : (I₂ ⊗ I₂) * (ket0 ⊗ ket0) = (I₂ * ket0) ⊗ (I₂ * ket0) := by
        convert L13_kron_mul_kron _ _ _ _ using 1;
      rw [ show ket000 = ket0 ⊗ ( ket0 ⊗ ket0 ) by rfl, h_mixed, h_expand, H_ket0, I2_ket0 ]

/-
Layer 2: (CX ⊗ I₂) × (|+⟩ ⊗ |00⟩)
    First expand CX = B₀ ⊗ I₂ + B₃ ⊗ X, then distribute.
    = (1/√2)(|0⟩ ⊗ |0⟩ ⊗ |0⟩) + (1/√2)(|1⟩ ⊗ |1⟩ ⊗ |0⟩)
-/
theorem ghz_layer2 :
    (CX ⊗ I₂) * (ket_plus ⊗ (ket0 ⊗ ket0)) =
    s2 • (ket0 ⊗ (ket0 ⊗ ket0)) + s2 • (ket1 ⊗ (ket1 ⊗ ket0)) := by
      ext i j;
      simp +decide [ Matrix.mul_apply, CX, ket0, ket1, ket_plus, s2 ];
      simp +decide [ B0, B3, X_gate, I₂, kron, Fin.sum_univ_succ ];
      fin_cases i <;> simp +decide [ Fin.modNat, Fin.divNat ];
      · simp +decide [ Matrix.one_apply ];
      · simp +decide [ B1, B2 ];
      · simp +decide [B1, B2];
        rfl

/-
Layer 3: (I₂ ⊗ CX) × intermediate = (1/√2)|000⟩ + (1/√2)|111⟩
-/

theorem ghz_layer3 :
    (I₂ ⊗ CX) * (s2 • (ket0 ⊗ (ket0 ⊗ ket0)) + s2 • (ket1 ⊗ (ket1 ⊗ ket0))) =
    s2 • ket000 + s2 • ket111 := by
      ext i j;
      simp_all +decide [ I₂, CX, B0, B3, X_gate, B1, B2, kron, ket0, ket1, ket000, ket111, Fin.divNat, Fin.modNat, Matrix.mul_apply, Fin.sum_univ_succ ];
      fin_cases i <;> simp +decide [ Fin.modNat ];
      · simp +decide [ Matrix.one_apply ];
      · rfl

/-- The main GHZ theorem: the full circuit produces the GHZ state.
    (I₂ ⊗ CX) × (CX ⊗ I₂) × (H ⊗ I₂ ⊗ I₂) × |000⟩ = (1/√2)(|000⟩ + |111⟩) -/
theorem ghz_circuit :
    (I₂ ⊗ CX) * ((CX ⊗ I₂) * ((H_gate ⊗ (I₂ ⊗ I₂)) * ket000)) =
    s2 • ket000 + s2 • ket111 := by
  rw [ghz_layer1, ghz_layer2, ghz_layer3]

end DiracRepr
end
