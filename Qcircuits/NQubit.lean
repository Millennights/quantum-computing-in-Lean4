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


/-! ## Key QFT theorems -/

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


end DiracRepr
end
