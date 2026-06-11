import Qcircuits.Strategies
import Qcircuits.Density

open Matrix Complex

noncomputable section

namespace DiracRepr


/-! ## N-qubit standard states -/

/-- |0⟩^⊗n -/
def ket0_n : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin 1) ℂ
  | 0 => !![1]
  | n + 1 => ket0_n n ⊗ ket0

/-- |1⟩^⊗n -/
def ket1_n : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin 1) ℂ
  | 0 => !![1]
  | n + 1 => ket1_n n ⊗ ket1

/-- |+⟩^⊗n -/
def ketp_n : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin 1) ℂ
  | 0 => !![1]
  | n + 1 => ketp_n n ⊗ ket_plus

/-- |−⟩^⊗n -/
def ketm_n : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin 1) ℂ
  | 0 => !![1]
  | n + 1 => ketm_n n ⊗ ket_minus

/-- ⟨0|^⊗n -/
def bra0_n : (n : ℕ) → Matrix (Fin 1) (Fin (2 ^ n)) ℂ
  | 0 => !![1]
  | n + 1 => bra0_n n ⊗ bra0

/-- ⟨1|^⊗n -/
def bra1_n : (n : ℕ) → Matrix (Fin 1) (Fin (2 ^ n)) ℂ
  | 0 => !![1]
  | n + 1 => bra1_n n ⊗ bra1


/-! ## N-qubit gates -/

/-- H^⊗n -/
def H_n : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | n + 1 => H_n n ⊗ H_gate

/-- I₂^⊗n : the n-qubit identity (equals the identity matrix) -/
def I₂_n : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | n + 1 => I₂_n n ⊗ I₂


/-! ## Simp lemmas -/

@[simp] theorem ket0_n_zero : ket0_n 0 = !![1] := rfl
@[simp] theorem ket0_n_succ (n : ℕ) : ket0_n (n + 1) = ket0_n n ⊗ ket0 := rfl
@[simp] theorem ketp_n_zero : ketp_n 0 = !![1] := rfl
@[simp] theorem ketp_n_succ (n : ℕ) : ketp_n (n + 1) = ketp_n n ⊗ ket_plus := rfl
@[simp] theorem ketm_n_zero : ketm_n 0 = !![1] := rfl
@[simp] theorem ketm_n_succ (n : ℕ) : ketm_n (n + 1) = ketm_n n ⊗ ket_minus := rfl
@[simp] theorem H_n_zero : H_n 0 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl
@[simp] theorem H_n_succ (n : ℕ) : H_n (n + 1) = H_n n ⊗ H_gate := rfl
@[simp] theorem I₂_n_zero : I₂_n 0 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl
@[simp] theorem I₂_n_succ (n : ℕ) : I₂_n (n + 1) = I₂_n n ⊗ I₂ := rfl
@[simp] theorem bra0_n_zero : bra0_n 0 = !![1] := rfl
@[simp] theorem bra0_n_succ (n : ℕ) : bra0_n (n + 1) = bra0_n n ⊗ bra0 := rfl
@[simp] theorem bra1_n_zero : bra1_n 0 = !![1] := rfl
@[simp] theorem bra1_n_succ (n : ℕ) : bra1_n (n + 1) = bra1_n n ⊗ bra1 := rfl

/-! ## I₂_n is the identity matrix -/

theorem I₂_n_eq_one : ∀ n, I₂_n n = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    simp only [I₂_n_succ, ih, I₂]
    exact L8_kron_one


/-! ## theorems -/

/-- H^⊗n × |0⟩^⊗n = |+⟩^⊗n -/
theorem QFT_ket0_n : ∀ n, H_n n * ket0_n n = ketp_n n := by
  intro n
  induction' n with n ih;
  · simp +decide [ H_n, ket0_n, ketp_n ];
  · convert congr_arg₂ ( fun x y => x ⊗ y ) ih ( H_ket0 ) using 1;
    convert L13_kron_mul_kron _ _ _ _ using 1

/-- H^⊗n × |+⟩^⊗n = |0⟩^⊗n -/
theorem QFT_ketp_n : ∀ n, H_n n * ketp_n n = ket0_n n := by
  intro n
  induction' n with n ih;
  · simp +decide [ H_n, ket0_n, ketp_n ];
  · convert congr_arg₂ ( fun x y => x ⊗ y ) ih ( H_ket_plus ) using 1;
    convert L13_kron_mul_kron _ _ _ _ using 1

/-- H^⊗n × |1⟩^⊗n = |-⟩^⊗n -/
theorem QFT_ket1_n : ∀ n, H_n n * ket1_n n = ketm_n n := by
  intro n
  induction' n with n ih;
  · simp +decide [ H_n, ket1_n, ketm_n ];
  · convert congr_arg₂ ( fun x y => x ⊗ y ) ih ( H_ket1 ) using 1;
    convert L13_kron_mul_kron _ _ _ _ using 1

/-- H^⊗n × |1⟩^⊗n = |-⟩^⊗n -/
theorem QFT_ketm_n : ∀ n, H_n n * ketm_n n = ket1_n n := by
  intro n
  induction' n with n ih;
  · simp +decide [ H_n, ket1_n, ketm_n ];
  · convert congr_arg₂ ( fun x y => x ⊗ y ) ih ( H_ket_minus ) using 1;
    convert L13_kron_mul_kron _ _ _ _ using 1

/-- ⟨0|^⊗n = (|0⟩^⊗n)ᴴ -/
theorem bra0_n_eq_conjTranspose (n : ℕ) : bra0_n n = (ket0_n n)ᴴ := by
  induction' n with n ih;
  · ext i j; fin_cases i; fin_cases j; simp +decide ;
  · convert congr_arg₂ ( fun x y => x ⊗ y ) ih ( bra0_eq_conjTranspose_ket0 ) using 1;
    convert L15_conjTranspose_kron _ _ using 1

/-- ⟨0|^⊗n · |0⟩^⊗n = 1 -/
theorem bra0_n_ket0_n (n : ℕ) :
    bra0_n n * ket0_n n = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  induction' n with n ih;
  · norm_num [bra0_n, ket0_n];
    exact Matrix.ext fun i j => by fin_cases i; fin_cases j; rfl;
  · have h_step : bra0_n (n + 1) * ket0_n (n + 1) = (bra0_n n ⊗ bra0) * (ket0_n n ⊗ ket0) := by
      rfl;
    rw [ h_step, L13_kron_mul_kron ];
    rw [ ih, L1_bra0_ket0, L8_kron_one ]


/-! ## Density matrix versions -/

/-- Density matrix version of QFT:
    super (H^⊗n) (density |0⟩^⊗n) = density |+⟩^⊗n -/
theorem DQFT_ket0_n (n : ℕ) :
    super (H_n n) (density (ket0_n n)) = density (ketp_n n) := by
  rw [super_density, QFT_ket0_n]

/-- Density matrix version of inverse QFT:
    super (H^⊗n) (density |+⟩^⊗n) = density |0⟩^⊗n -/
theorem DQFT_ketp_n (n : ℕ) :
    super (H_n n) (density (ketp_n n)) = density (ket0_n n) := by
  rw [super_density, QFT_ketp_n]


/-! ## Standard Basis Properties -/

/-- Standard basis column vector |x⟩ ∈ ℂ^m -/
def stdKet {m : ℕ} (x : Fin m) : Matrix (Fin m) (Fin 1) ℂ :=
  Matrix.of fun i _ => if i = x then 1 else 0

/-- Standard basis row vector ⟨x| ∈ ℂ^{1×m} -/
def stdBra {m : ℕ} (x : Fin m) : Matrix (Fin 1) (Fin m) ℂ :=
  Matrix.of fun _ j => if j = x then 1 else 0

/-- The conjugate transpose of a standard ket is the corresponding standard bra. -/
theorem stdKet_conjTranspose {m : ℕ} (x : Fin m) : (stdKet x)ᴴ = stdBra x := by
  ext i j
  simp [stdKet, stdBra, Matrix.conjTranspose_apply, apply_ite]

/-- Standard basis projector |x⟩⟨x| -/
def stdProj {m : ℕ} (x : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  stdKet x * stdBra x

/-- stdProj is a matrix with 1 at (x,x) and 0 elsewhere -/
theorem stdProj_apply {m : ℕ} (x : Fin m) (i j : Fin m) :
    stdProj x i j = if i = x ∧ j = x then 1 else 0 := by
  unfold stdProj stdKet stdBra;
  rw [ Matrix.mul_apply ] ; aesop

/-- `|0⟩^⊗n` is the standard basis ket at index `0`. -/
theorem ket0_n_eq_stdKet (n : ℕ) : ket0_n n = stdKet (0 : Fin (2 ^ n)) := by
  induction' n with n ih;
  · ext i j; fin_cases i; fin_cases j; simp +decide [ stdKet ] ;
  · convert congr_arg ( fun x => x ⊗ ket0 ) ih using 1;
    ext i j;
    simp +decide [ stdKet, ket0, kron ];
    rcases i with ⟨ _ | i, hi ⟩ <;> simp +decide [Fin.ext_iff] at hi ⊢;
    · rfl;
    · rcases i with ( _ | _ | i ) <;> tauto

/-- `⟨x| · |y⟩ = δ(x,y)` for standard basis vectors. -/
theorem stdBra_stdKet {n : ℕ} (x y : Fin (2 ^ n)) :
    stdBra x * stdKet y = if x = y then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0 := by
  unfold stdBra stdKet; ext i j; simp +decide [ Matrix.mul_apply ] ;
  fin_cases i ; fin_cases j ; aesop

/-- `|x⟩⟨x| · |y⟩ = δ(x,y) |x⟩`. -/
theorem stdProj_stdKet {n : ℕ} (x y : Fin (2 ^ n)) :
    stdProj x * stdKet y = if x = y then stdKet x else 0 := by
  unfold stdProj;
  convert congr_arg ( fun m => stdKet x * m ) ( DiracRepr.stdBra_stdKet x y ) using 1 ; norm_num [ Matrix.mul_assoc ];
  aesop

/-- Tensor product distributes over finite sums on the left -/
theorem kron_sum_left {m n p q : ℕ} (s : Finset ι)
    (A : ι → Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    (∑ i ∈ s, A i) ⊗ B = ∑ i ∈ s, (A i ⊗ B) := by
  ext i j;
  simp +decide [Matrix.sum_apply];
  simp +decide [ kron ];
  rw [ ← Finset.sum_mul _ _ _, Matrix.sum_apply ]

/-- Tensor product distributes over finite sums on the right -/
theorem kron_sum_right {m n p q : ℕ} (s : Finset ι)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : ι → Matrix (Fin p) (Fin q) ℂ) :
    A ⊗ (∑ i ∈ s, B i) = ∑ i ∈ s, (A ⊗ B i) := by
  ext i j; simp [kron];
  simp +decide [ Matrix.sum_apply, Finset.mul_sum _ _ _ ]


/-! #### Helper lemmas for the amplitude computation -/

/-- Every entry of ketp_n n equals root2^n (uniform superposition) -/
theorem ketp_n_entry (n : ℕ) (i : Fin (2 ^ n)) :
    (ketp_n n) i 0 = (s2 : ℂ) ^ n := by
  induction' n with n ih;
  · fin_cases i ; rfl;
  · convert congr_arg₂ ( · * · ) ( ih ( i.divNat ) ) ( show ket_plus ( i.modNat ) 0 = s2 from ?_ ) using 1;
    rcases i.modNat with ( _ | _ | i ) <;> norm_num [ ket_plus ]

/-- Entries of ketp_n are real -/
theorem ketp_n_entry_conj (n : ℕ) (i : Fin (2 ^ n)) :
    starRingEnd ℂ ((ketp_n n) i 0) = (ketp_n n) i 0 := by
  rw [ ketp_n_entry ] ; norm_num [ Complex.ext_iff, pow_succ ] ; ring;
  erw [ Complex.conj_ofReal ] ; norm_num

/-- s2² = 1/2 in ℂ -/
theorem s2_sq : (s2 : ℂ) ^ 2 = 1 / 2 := by
  norm_num [ Complex.ext_iff, sq ];
  ring_nf; norm_num;

/-- Hᴴ = H -/
theorem H_gate_conjTranspose : (H_gate)ᴴ = H_gate := by
  unfold H_gate;
  unfold B0 B1 B2 B3; norm_num [ ← Matrix.ext_iff ] ;
  erw [ Complex.conj_ofReal ] ; norm_num

/-- H_n is Hermitian (self-adjoint) -/
theorem H_n_conjTranspose (n : ℕ) : (H_n n)ᴴ = H_n n := by
  induction' n with n ih
  · exact Matrix.conjTranspose_one
  · ext i j
    simp only [H_n_succ, Matrix.conjTranspose_apply, kron, star_mul', Matrix.of_apply]
    have h1 := congr_fun (congr_fun ih (i.divNat)) (j.divNat)
    simp only [Matrix.conjTranspose_apply] at h1
    have h2 := congr_fun (congr_fun H_gate_conjTranspose (i.modNat)) (j.modNat)
    simp only [Matrix.conjTranspose_apply] at h2
    rw [h1, h2]

/-- bra0_n * H_n = (ketp_n)ᴴ -/
theorem bra0_n_mul_H_n (n : ℕ) :
    bra0_n n * H_n n = (ketp_n n)ᴴ := by
  rw [ ← QFT_ket0_n ];
  simp +decide [H_n_conjTranspose];
  rw [ bra0_n_eq_conjTranspose ]

end DiracRepr
end
