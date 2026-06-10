import Qcircuits.Basic

open Matrix Complex DiracRepr

noncomputable section

namespace DiracRepr

/-! ## L1: Inner products of basis states
  ⟨0|0⟩ = ⟨1|1⟩ = 1, ⟨0|1⟩ = ⟨1|0⟩ = 0
-/

theorem L1_bra0_ket0 : bra0 * ket0 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j ; fin_cases i ; fin_cases j ; norm_num [ Matrix.mul_apply, bra0, ket0 ]

theorem L1_bra1_ket1 : bra1 * ket1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j; simp [bra1, ket1];
  simp [Fin.eq_zero, Matrix.one_apply]

theorem L1_bra0_ket1 : bra0 * ket1 = (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j; simp [bra0, ket1]

theorem L1_bra1_ket0 : bra1 * ket0 = (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j; simp [bra1, ket0]


/-! ## L2: Associativity of scalar product, matrix product, addition, and tensor product
-/

/-
Matrix multiplication associativity: `Matrix.mul_assoc`
-/
theorem L2_mul_assoc {l m n p : ℕ}
    (A : Matrix (Fin l) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin n) (Fin p) ℂ) :
    A * B * C = A * (B * C) := by
      convert Matrix.mul_assoc A B C

/-
Matrix addition associativity: `add_assoc`
-/
theorem L2_add_assoc {m n : ℕ}
    (A B C : Matrix (Fin m) (Fin n) ℂ) : A + B + C = A + (B + C) := by
      rw [ add_assoc ]

/-
Tensor product associativity (stated via submatrix cast since (a*c)*e ≠ a*(c*e) definitionally)
(m * p) * r 与 m * (p * r) 在 Lean 中是不同的类型，但它们是同构的，因此我们可以通过一个子矩阵转换来表达它们之间的关系。
-/
theorem L2_kron_assoc {a b c d e f : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin c) (Fin d) ℂ) (C : Matrix (Fin e) (Fin f) ℂ) :
    ∀ (i : Fin ((a * c) * e)) (j : Fin ((b * d) * f)),
      ((A ⊗ B) ⊗ C) i j =
        (A ⊗ (B ⊗ C))
          ⟨i.val, Nat.mul_assoc a c e ▸ i.isLt⟩
          ⟨j.val, Nat.mul_assoc b d f ▸ j.isLt⟩ := by
            intro i j;
            -- Using the definitions of `Fin.divNat` and `Fin.modNat`, we can rewrite the indices.
            have h_div_mod : ∀ (i : Fin (a * c * e)) (j : Fin (b * d * f)),
              (i.val / (e) / (c)) = (i.val / (c) / (e)) ∧
              (i.val / (e) % (c)) = (i.val % (c * e) / (e)) ∧
              (j.val / (f) / (d)) = (j.val / (d) / (f)) ∧
              (j.val / (f) % (d)) = (j.val % (d * f) / (f)) := by
                intros i j; exact ⟨by
                rw [ Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul ];
                lia, by
                  rw [ ← Nat.mod_add_div i ( c * e ) ] ; norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod_mul_right ] ;
                  rcases e with ( _ | _ | e ) <;> rcases c with ( _ | _ | c ) <;> norm_num [ Nat.add_div, Nat.mul_div_assoc ] at *;
                  · norm_num [ Nat.mod_one ];
                  · grind;
                  · norm_num [ Nat.mul_assoc, Nat.mul_div_assoc ];
                    norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ];
                    split_ifs <;> simp_all +decide;
                    · linarith [ Nat.mod_lt ( i : ℕ ) ( by linarith : 0 < e + 1 + 1 ) ];
                    · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.mod_lt ( i : ℕ ) ( by positivity : 0 < ( c + 1 + 1 ) * ( e + 1 + 1 ) ) ] ), by
                  rw [ Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul ] ; ring_nf, by
                  rw [ ← Nat.mod_add_div j ( d * f ) ] ; ring_nf; norm_num [ Nat.add_mul_div_right, Nat.mul_mod_mul_right ] ;
                  rcases d with ( _ | d ) <;> rcases f with ( _ | f ) <;> norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod_mul_left ] at *;
                  norm_num [ Nat.mul_assoc, Nat.mul_div_assoc ];
                  norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ];
                  split_ifs <;> norm_num [ Nat.mod_eq_of_lt ];
                  · linarith [ Nat.mod_lt ( j : ℕ ) ( Nat.succ_pos f ) ];
                  · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.mod_lt ( j : ℕ ) ( by positivity : 0 < ( d + 1 ) * ( f + 1 ) ) ] )⟩;
            unfold kron;
            simp +decide [ Fin.divNat, Fin.modNat, h_div_mod i j ];
            simp +decide only [Nat.div_div_eq_div_mul, mul_assoc]


/-! ## L3: Scalar multiplication with 0 and 1
  0 • A = 0,  c • 0 = 0,  1 • A = A
-/

theorem L3_zero_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (0 : ℂ) • A = 0 := by
      convert zero_smul ℂ A

theorem L3_smul_zero {m n : ℕ} (c : ℂ) :
    c • (0 : Matrix (Fin m) (Fin n) ℂ) = 0 := by
      norm_num +zetaDelta at *

theorem L3_one_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (1 : ℂ) • A = A := by
      norm_num


/-! ## L4: Scalar multiplication distributes over addition
  c • (A + B) = c • A + c • B
-/

theorem L4_smul_add {m n : ℕ} (c : ℂ) (A B : Matrix (Fin m) (Fin n) ℂ) :
    c • (A + B) = c • A + c • B := by
      ext i j; simp;
      ring


/-! ## L5: Scalar multiplication distributes into matrix product
  c • (A × B) = (c • A) × B = A × (c • B)
-/

theorem L5_smul_mul_left {m n p : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    c • (A * B) = (c • A) * B := by
      exact Eq.symm (smul_mul c A B)

theorem L5_smul_mul_right {m n p : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    c • (A * B) = A * (c • B) := by
      ext i j; simp +decide [ Matrix.mul_apply] ;
      simp +decide only [Finset.mul_sum _ _ _, mul_left_comm]


/-! ## L6: Scalar multiplication distributes into tensor product
  c • (A ⊗ B) = (c • A) ⊗ B = A ⊗ (c • B)
-/

theorem L6_smul_kron_left {m n p q : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    c • (A ⊗ B) = (c • A) ⊗ B := by
      ext i j; simp +decide [ kron ] ; ring;

theorem L6_smul_kron_right {m n p q : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    c • (A ⊗ B) = A ⊗ (c • B) := by
      -- By definition of scalar multiplication and the Kronecker product, we can show that each element of the matrices is equal.
      ext i j; simp [kron, Matrix.smul_apply];
      ring


/-! ## L7: Multiplication by zero matrix
  0 × A = 0,  A × 0 = 0
-/

theorem L7_zero_mul {m n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) :
    (0 : Matrix (Fin m) (Fin n) ℂ) * A = 0 := by
      ext i j; simp +decide [ Matrix.mul_apply ] ;

theorem L7_mul_zero {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    A * (0 : Matrix (Fin n) (Fin p) ℂ) = 0 := by
      convert Matrix.mul_zero _


/-! ## L8: Identity matrix laws
  I × A = A,  A × I = A,  I ⊗ I = I
-/

theorem L8_one_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (1 : Matrix (Fin m) (Fin m) ℂ) * A = A := by
      convert Matrix.one_mul A

theorem L8_mul_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    A * (1 : Matrix (Fin n) (Fin n) ℂ) = A := by
      convert Matrix.mul_one A

theorem L8_kron_one {m n : ℕ} :
    (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ (1 : Matrix (Fin n) (Fin n) ℂ) =
    (show Matrix (Fin (m * n)) (Fin (m * n)) ℂ from 1) := by
      ext i j; by_cases hij : i = j <;> simp_all +decide [ Matrix.one_apply, kron ] ;
      simp_all +decide [ Fin.ext_iff, Fin.modNat, Fin.divNat ];
      exact fun h => fun h' => hij <| by nlinarith [ Nat.mod_add_div i n, Nat.mod_add_div j n ] ;


/-! ## L9: Addition with zero
  0 + A = A,  A + 0 = A
-/

theorem L9_zero_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (0 : Matrix (Fin m) (Fin n) ℂ) + A = A := by
      -- By definition of matrix addition, adding the zero matrix to any matrix results in the original matrix. This follows from the fact that addition of complex numbers is commutative and associative.
      simp

theorem L9_add_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    A + (0 : Matrix (Fin m) (Fin n) ℂ) = A := by
      -- By definition of matrix addition, adding the zero matrix to any matrix results in the original matrix.
      simp [add_zero]


/-! ## L10: Tensor product with zero
  0 ⊗ A = 0,  A ⊗ 0 = 0
-/

theorem L10_kron_zero_left {m n p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    (0 : Matrix (Fin m) (Fin n) ℂ) ⊗ A = 0 := by
      ext i j; simp [kron]

theorem L10_kron_zero_right {m n p q : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    A ⊗ (0 : Matrix (Fin p) (Fin q) ℂ) = 0 := by
      -- By definition of tensor product, we know that $(A \otimes 0)_{ij} = A_{ij} \cdot 0_{ij}$.
      ext i j; simp [kron]


/-! ## L11: Distributivity of matrix product over addition
  (A + B) × C = A × C + B × C,  C × (A + B) = C × A + C × B
-/

theorem L11_add_mul {m n p : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin n) (Fin p) ℂ) :
    (A + B) * C = A * C + B * C := by
      exact Matrix.add_mul A B C

theorem L11_mul_add {m n p : ℕ}
    (C : Matrix (Fin m) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin p) ℂ) :
    C * (A + B) = C * A + C * B := by
      exact Matrix.mul_add C A B


/-! ## L12: Distributivity of tensor product over addition
  (A + B) ⊗ C = A ⊗ C + B ⊗ C,  C ⊗ (A + B) = C ⊗ A + C ⊗ B
-/

theorem L12_add_kron_left {m n p q : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin p) (Fin q) ℂ) :
    (A + B) ⊗ C = A ⊗ C + B ⊗ C := by
      ext ⟨ i, hi ⟩ ⟨ j, hj ⟩;
      simp [kron, Matrix.add_apply];
      ring

theorem L12_add_kron_right {m n p q : ℕ}
    (C : Matrix (Fin m) (Fin n) ℂ) (A B : Matrix (Fin p) (Fin q) ℂ) :
    C ⊗ (A + B) = C ⊗ A + C ⊗ B := by
      ext ⟨ i, hi ⟩ ⟨ j, hj ⟩;
      unfold kron;
      simp +decide [ mul_add ]


/-! ## L13: Mixed product property
  (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D)
  This is the key law enabling symbolic reasoning about tensor products.
-/

theorem L13_kron_mul_kron {a b c d e f : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin c) (Fin d) ℂ)
    (C : Matrix (Fin b) (Fin e) ℂ) (D : Matrix (Fin d) (Fin f) ℂ) :
    (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D) := by
      convert Matrix.ext _;
      intro i j; simp +decide [ Matrix.mul_apply, kron ];
      simp +decide only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _];
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun x _ => ⟨ ⟨ x % d, Nat.mod_lt _ ( by
        cases d <;> aesop ) ⟩, ⟨ x / d, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt x ] ⟩ ⟩ ) _ _ _ _ <;> simp +decide;
      · exact fun a₁ a₂ h₁ h₂ => Fin.ext <| by nlinarith [ Nat.mod_add_div a₁ d, Nat.mod_add_div a₂ d ] ;
      · rintro ⟨ ⟨ i, hi ⟩, ⟨ j, hj ⟩ ⟩ ; use ⟨ i + j * d, by nlinarith ⟩ ; simp +decide [Nat.mod_eq_of_lt,
        hi] ;
        rw [ Nat.add_mul_div_right _ _ ( by linarith ) ] ; aesop;
      · bound


/-! ## L14: Conjugate transpose of scalar product and matrix product
  (c • A)ᴴ = conj(c) • Aᴴ,  (A × B)ᴴ = Bᴴ × Aᴴ
-/

theorem L14_conjTranspose_smul {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    (c • A)ᴴ = starRingEnd ℂ c • Aᴴ := by
      ext i j; simp +decide [ Matrix.conjTranspose_apply ]

theorem L14_conjTranspose_mul {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    (A * B)ᴴ = Bᴴ * Aᴴ := by
      -- Apply the lemma that states the conjugate transpose of a product is the product of the conjugate transposes in reverse order, which is `Matrix.conjTranspose_mul`.
      apply Matrix.conjTranspose_mul


/-! ## L15: Conjugate transpose of addition and tensor product
  (A + B)ᴴ = Aᴴ + Bᴴ,  (A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ
-/

theorem L15_conjTranspose_add {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (A + B)ᴴ = Aᴴ + Bᴴ := by
      exact conjTranspose_add A B

theorem L15_conjTranspose_kron {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    (A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ := by
      ext i j;
      unfold Matrix.conjTranspose kron;
      simp +decide


/-! ## L16: Double conjugate transpose
  (Aᴴ)ᴴ = A
-/

theorem L16_conjTranspose_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Aᴴᴴ = A := by
      exact conjTranspose_conjTranspose A


/-! ## Bras are conjugate transposes of kets -/

theorem bra0_eq_conjTranspose_ket0 :
  bra0 = ket0ᴴ := by
  ext i j;
  fin_cases i ; fin_cases j <;> norm_num [ DiracRepr.ket0, DiracRepr.bra0 ]

theorem bra1_eq_conjTranspose_ket1 :
  bra1 = ket1ᴴ := by
  ext i j; simp [bra1, ket1];
  fin_cases j <;> norm_num

end DiracRepr
end
