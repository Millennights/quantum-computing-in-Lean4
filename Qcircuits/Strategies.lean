import Qcircuits.Laws

open Matrix Complex DiracRepr

noncomputable section

namespace DiracRepr

/-- B₀ = |0⟩⟨0| -/
theorem B0_ket0 : B0 * ket0 = ket0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B0, ket0 ] ;

theorem B0_ket1 : B0 * ket1 = 0 := by
  -- By definition of B0 and ket1, we can compute the product directly.
  simp [B0, ket1];
  -- The matrix !![0; 0] is equal to the zero matrix because both rows are zeros.
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- B₁ = |0⟩⟨1| -/
theorem B1_ket0 : B1 * ket0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, B1, bra0 ] ;

theorem B1_ket1 : B1 * ket1 = ket0 := by
  -- By definition of matrix multiplication, we can compute each element of the resulting matrix.
  ext i j; simp [B1, ket1]

/-- B₂ = |1⟩⟨0| -/
theorem B2_ket0 : B2 * ket0 = ket1 := by
  ext i
  simp [B2, ket0, Matrix.mul_apply]

theorem B2_ket1 : B2 * ket1 = 0 := by
  -- By definition of $B2$, we have $B2 = |1⟩⟨0|$.
  simp [B2];
  -- By definition of matrix equality, we need to show that all elements of the matrix are zero.
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- B₃ = |1⟩⟨1| -/
theorem B3_ket0 : B3 * ket0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B3, B2, B1, B0, ket1, ket0, bra1, bra0 ] ;

theorem B3_ket1 : B3 * ket1 = ket1 := by
  ext i j;
  -- By definition of matrix multiplication, we can expand the product B3 * ket1.
  simp [B3, ket1]


/-! ### B_i acting on |+⟩ and |−⟩ -/

theorem B0_ket_plus : B0 * ket_plus = s2 • ket0 := by
  unfold ket_plus B0;
  ext i j;
  fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ]

theorem B0_ket_minus : B0 * ket_minus = s2 • ket0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B0, B1, B2, B3, ket_minus ] at *;

theorem B1_ket_plus : B1 * ket_plus = s2 • ket0 := by
  ext i j;
  fin_cases i <;> fin_cases j <;> norm_num [ B1, ket0, ket1 ];
  norm_num [ Matrix.vecMul, ket_plus ];
  norm_num [ vecHead, vecTail ]

theorem B1_ket_minus : B1 * ket_minus = (-s2) • ket0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B1, B2, B3, ket0, ket1, bra0, bra1, Matrix.mul_apply ];
  unfold ket_minus; norm_num [ Complex.ext_iff, Real.sqrt_div_self ] ;

theorem B2_ket_plus : B2 * ket_plus = s2 • ket1 := by
  unfold ket_plus;
  rw [ Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul ];
  rw [ B2_ket0, B2_ket1 ] ; norm_num

theorem B2_ket_minus : B2 * ket_minus = s2 • ket1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B2, B3, B0, B1, ket_minus ] at *;

theorem B3_ket_plus : B3 * ket_plus = s2 • ket1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ B3, B2, B1, B0, ket1, ket0, ket_plus, Matrix.mul_apply ] ;

theorem B3_ket_minus : B3 * ket_minus = (-s2) • ket1 := by
  ext i;
  fin_cases i <;> norm_num [ B3, ket_minus ]


/-! ### Identity gate -/

theorem I2_ket0 : I₂ * ket0 = ket0 := by
  simp +decide [ I₂ ]

theorem I2_ket1 : I₂ * ket1 = ket1 := by
  -- The identity matrix multiplied by any vector is the vector itself.
  simp [I₂]


/-! ### Pauli-X gate: X|0⟩ = |1⟩, X|1⟩ = |0⟩ -/

theorem X_ket0 : X_gate * ket0 = ket1 := by
  unfold X_gate; simp +decide ;
  unfold B1 B2; norm_num [ Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc ]

theorem X_ket1 : X_gate * ket1 = ket0 := by
  -- Substitute the definitions of X_gate and ket1.
  rw [show X_gate = B1 + B2 from rfl]
  rw [show ket1 = !![0; 1] from rfl];
  -- Substitute the definitions of B1 and B2 into the expression.
  simp [B1, B2]

/-! ### Pauli-Y gate: Y|0⟩ = i|1⟩, Y|1⟩ = -i|0⟩ -/

theorem Y_ket0 : Y_gate * ket0 = I • ket1 := by
  ext i;
  fin_cases i <;> simp +decide [ Y_gate, B1, B2, DiracRepr.ket0, DiracRepr.ket1, Matrix.mul_apply ]

theorem Y_ket1 : Y_gate * ket1 = (-I) • ket0 := by
  unfold Y_gate
  simp [B1, B2]

/-! ### Pauli-Z gate: Z|0⟩ = |0⟩, Z|1⟩ = -|1⟩ -/

theorem Z_ket0 : Z_gate * ket0 = ket0 := by
  ext i;
  fin_cases i <;> simp +decide [ Z_gate, B0, B3, ket0 ]

theorem Z_ket1 : Z_gate * ket1 = -ket1 := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Z_gate, B0, B3, Matrix.mul_apply ]


/-! ### Hadamard gate: H|0⟩ = |+⟩, H|1⟩ = |−⟩ -/

theorem H_ket0 : H_gate * ket0 = ket_plus := by
  unfold H_gate ket_plus;
  simp +decide [ B0, B1, B2, B3 ]

theorem H_ket1 : H_gate * ket1 = ket_minus := by
  unfold H_gate;
  simp +decide [ B0, B1, B2, B3 ];
  unfold ket_minus; ext i j; fin_cases i <;> fin_cases j <;> norm_num [ ket0, ket1 ] ;


/-! ### Gates acting on |+⟩ and |−⟩ -/

theorem H_ket_plus : H_gate * ket_plus = ket0 := by
  unfold H_gate;
  unfold s2; norm_num [ B0, B1, B2, B3, ket_plus ] ;
  ring_nf;norm_num [ ← Complex.ofReal_pow ] ;

theorem H_ket_minus : H_gate * ket_minus = ket1 := by
  -- Expand H_gate using its definition and simplify each term.
  simp [H_gate, B0, B1, B2, B3, ket0, ket1, ket_minus];
  ring_nf; norm_num [ ← Complex.ofReal_pow ] ;

theorem X_ket_plus : X_gate * ket_plus = ket_plus := by
  unfold X_gate ket_plus;
  norm_num [ B1, B2, ket0, ket1, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul ]

theorem X_ket_minus : X_gate * ket_minus = -ket_minus := by
  unfold ket_minus;
  simp +decide [DiracRepr.X_gate];
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, B1, B2 ]

theorem Z_ket_plus : Z_gate * ket_plus = ket_minus := by
  unfold Z_gate ket_plus ket_minus;
  unfold B0 B3; ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply ] ;

theorem Z_ket_minus : Z_gate * ket_minus = ket_plus := by
  unfold Z_gate ket_minus;
  simp +decide [ B0, B3, ket_plus ]

end DiracRepr
end
