import Qcircuits.DeutschJozsa

open Matrix Complex

noncomputable section

namespace DiracRepr

/-!
We reuse the general oracle `Uf_general`, the phase-kickback lemma
`oracle_on_ketp_minus`, and the output state `DJ_output` from `DeutschJozsa.lean`.
-/


/-! ## Bitwise dot-product sign -/

/-- The bitwise dot product (mod 2) of `a` and `b`, as a `Bool`.
    `bdot_BV a b = true` iff the number of positions where both `a` and `b` have a
    `1` bit is odd.  Defined by recursion on the low bit. -/
def bdot_BV (a b : ℕ) : Bool :=
  if a = 0 then false
  else xor (decide (a % 2 = 1 ∧ b % 2 = 1)) (bdot_BV (a / 2) (b / 2))
termination_by a
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by norm_num)


/-- The sign `(-1)^{a·b}` associated to the bitwise dot product. -/
def dotSign (a b : ℕ) : ℂ := if bdot_BV a b then (-1 : ℂ) else 1

/- The single-step unfolding of `bdot_BV`, valid for all `a` (including `a = 0`). -/
theorem bdot_BV_step (a b : ℕ) :
    bdot_BV a b = xor (decide (a % 2 = 1 ∧ b % 2 = 1)) (bdot_BV (a / 2) (b / 2)) := by
  by_cases ha : a = 0;
  · unfold bdot_BV; simp +decide [ ha ];
  · rw [ bdot_BV ] ; aesop

@[simp] theorem bdot_BV_zero_left (b : ℕ) : bdot_BV 0 b = false := by
  unfold bdot_BV; simp

theorem dotSign_zero_left (b : ℕ) : dotSign 0 b = 1 := by
  simp [dotSign]

/-
`dotSign` is multiplicative in the first argument via bitwise XOR:
    `(-1)^{a·c} · (-1)^{b·c} = (-1)^{(a ⊕ b)·c}`.
-/
theorem dotSign_mul (a b c : ℕ) :
    dotSign a c * dotSign b c = dotSign (a ^^^ b) c := by
  -- By definition of dotSign, we need to show that bdot_BV a c + bdot_BV b c = bdot_BV (a ^^^ b) c.
  have h_dot_sign : ∀ a b c, bdot_BV (a ^^^ b) c = xor (bdot_BV a c) (bdot_BV b c) := by
    intros a b c; induction' a using Nat.binaryRec with a ih generalizing b c <;> induction' b using Nat.binaryRec with b ih' generalizing c <;> induction' c using Nat.binaryRec with c ih'' <;> simp_all +decide ;
    · unfold bdot_BV; simp +decide ;
      grind +splitIndPred;
    · unfold bdot_BV; simp +decide [ *, Nat.mod_two_of_bodd ] ;
      grind;
  unfold dotSign; aesop;


/-! ## Entry formula for the Walsh–Hadamard transform -/

/-- Entry of the single-qubit Hadamard gate: `H a b = s2 · (-1)^{a·b}`. -/
theorem H_gate_entry (a b : Fin 2) :
    H_gate a b = (s2 : ℂ) * (if a.val = 1 ∧ b.val = 1 then (-1 : ℂ) else 1) := by
  fin_cases a <;> fin_cases b <;>
    simp [H_gate, B0, B1, B2, B3, ket0, ket1, bra0, bra1]

/- Entry formula for `H^⊗n`: `(H^⊗n) i j = s2^n · (-1)^{i·j}`. -/
theorem H_n_entry (n : ℕ) (i j : Fin (2 ^ n)) :
    (H_n n) i j = (s2 : ℂ) ^ n * dotSign i.val j.val := by
  -- We proceed by induction on $n$.
  induction' n with n ih;
  · fin_cases i ; fin_cases j ; simp +decide [ dotSign ];
  · -- By definition of $H_n$, we have $H_n (n + 1) = H_n n ⊗ H_gate$.
    have hH_succ : H_n (n + 1) = H_n n ⊗ H_gate := by
      rfl;
    -- By definition of $bdot_BV$, we have $bdot_BV i.val j.val = xor (decide (i.val % 2 = 1 ∧ j.val % 2 = 1)) (bdot_BV (i.val / 2) (j.val / 2))$.
    have hbdot_BV_step : bdot_BV i.val j.val = xor (decide (i.val % 2 = 1 ∧ j.val % 2 = 1)) (bdot_BV (i.val / 2) (j.val / 2)) := by
      exact bdot_BV_step _ _;
    simp_all +decide [ dotSign ];
    convert congr_arg₂ ( · * · ) ( ih ⟨ i.val / 2, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt i, pow_succ' 2 n ] ⟩ ⟨ j.val / 2, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt j, pow_succ' 2 n ] ⟩ ) ( H_gate_entry ⟨ i.val % 2, Nat.mod_lt _ <| by decide ⟩ ⟨ j.val % 2, Nat.mod_lt _ <| by decide ⟩ ) using 1 ; norm_num [ pow_succ, mul_assoc, mul_comm, mul_left_comm ] ; ring;
    grind


/-! ## Orthogonality of characters -/

/-
Orthogonality of the additive characters of `(ℤ/2)^n`:
    `∑_{x < 2^n} (-1)^{t·x} = 2^n` if `t = 0`, and `0` otherwise (for `t < 2^n`).
-/
theorem dotSign_char_sum (n : ℕ) (t : ℕ) (ht : t < 2 ^ n) :
    ∑ x : Fin (2 ^ n), dotSign t x.val = if t = 0 then (2 ^ n : ℂ) else 0 := by
  induction' n with n ih generalizing t <;> simp_all +decide [pow_succ];
  · simp_all [dotSign]
  · -- Rewrite the sum over `Fin (2^(n+1))` as a double sum over `x' : Fin (2^n)` and `b : Fin 2`.
    have h_double_sum : ∑ x : Fin (2 ^ (n + 1)), dotSign t x.val = ∑ x' : Fin (2 ^ n), ∑ b : Fin 2, dotSign t (2 * x'.val + b.val) := by
      have h_double_sum : Finset.sum (Finset.range (2 ^ (n + 1))) (fun x => dotSign t x) = Finset.sum (Finset.range (2 ^ n)) (fun x' => Finset.sum (Finset.range 2) (fun b => dotSign t (2 * x' + b))) := by
        rw [ pow_succ' ];
        induction 2 ^ n <;> simp_all +decide [ Nat.mul_succ, Finset.sum_range_succ ] ; ring;
      simpa only [ Finset.sum_range, Fin.cast_val_eq_self ] using h_double_sum;
    -- By definition of `dotSign`, we have `dotSign t (2 * x'.val + b.val) = (if t % 2 = 1 ∧ b.val = 1 then (-1 : ℂ) else 1) * dotSign (t / 2) x'.val`.
    have h_dotSign : ∀ x' : Fin (2 ^ n), ∀ b : Fin 2, dotSign t (2 * x'.val + b.val) = (if t % 2 = 1 ∧ b.val = 1 then (-1 : ℂ) else 1) * dotSign (t / 2) x'.val := by
      intros x' b
      have h_bdot_BV : bdot_BV t (2 * x'.val + b.val) = xor (decide (t % 2 = 1 ∧ b.val = 1)) (bdot_BV (t / 2) x'.val) := by
        convert bdot_BV_step t ( 2 * x'.val + b.val ) using 1 ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.add_div ];
        fin_cases b <;> simp +decide;
      unfold dotSign; aesop;
    split_ifs <;> simp_all +decide [Finset.sum_add_distrib];
    · ring;
    · rcases Nat.even_or_odd' t with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [Nat.add_mod];
      rw [ ih k ( by linarith ) ] ; aesop


/-! ## The Bernstein–Vazirani amplitude -/

/-- The amplitude (up to the `1/2^n` normalisation) at computational basis state
    `|y⟩` after running the circuit on oracle `f`. -/
def bvAmp (n : ℕ) (f : Fin (2 ^ n) → Bool) (y : Fin (2 ^ n)) : ℂ :=
  ∑ x : Fin (2 ^ n), dotSign y.val x.val * (if f x then (-1 : ℂ) else 1)

/-- The measurement amplitude at `|y⟩ ⊗ |1⟩` equals `(1/2^n) · bvAmp`. -/
theorem BV_amplitude (n : ℕ) (f : Fin (2 ^ n) → Bool) (y : Fin (2 ^ n)) :
    (stdBra y ⊗ bra1) * DJ_output n f =
      (1 / (2 : ℂ) ^ n) • (bvAmp n f y) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  unfold DJ_output;
  -- Substitute the simplified forms of the matrices into the expression.
  have h_simp : stdBra y ⊗ bra1 * (H_n n ⊗ H_gate * (Uf_general n f * (H_n n ⊗ H_gate * (ket0_n n ⊗ ket1)))) = stdBra y ⊗ bra1 * ((H_n n * phaseVec n f) ⊗ ket1) := by
    have h_simp : Uf_general n f * (H_n n ⊗ H_gate * (ket0_n n ⊗ ket1)) = phaseVec n f ⊗ ket_minus := by
      rw [ ← oracle_on_ketp_minus, ← DJ_step1 ];
    rw [ h_simp, L13_kron_mul_kron ];
    rw [ H_ket_minus ];
  -- By definition of `stdBra` and `bra1`, we can simplify the expression.
  have h_simp' : stdBra y ⊗ bra1 * ((H_n n * phaseVec n f) ⊗ ket1) = (stdBra y * (H_n n * phaseVec n f)) ⊗ (bra1 * ket1) := by
    convert L13_kron_mul_kron ( stdBra y ) ( bra1 ) ( H_n n * phaseVec n f ) ( ket1 ) using 1;
  -- By definition of `stdBra` and `bra1`, we can simplify the expression further.
  have h_simp'' : stdBra y * (H_n n * phaseVec n f) = (1 / 2 ^ n : ℂ) • (bvAmp n f y : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i ; fin_cases j ; simp +decide [ Matrix.mul_apply, H_n_entry ] ; ring;
    simp +decide [ stdBra, phaseVec, bvAmp, dotSign ];
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; ring ; norm_num [ ← mul_pow ] ; ring;
    norm_cast ; norm_num [ pow_mul' ];
    norm_num [ ← mul_pow ];
  rw [ h_simp, h_simp', h_simp'' ];
  ext i j ; fin_cases i ; fin_cases j ; norm_num [ bra1, ket1 ];
  simp +decide [ Matrix.smul_eq_diagonal_mul ];
  exact mul_one _


/-! ## The Bernstein–Vazirani oracle -/

/-- The Bernstein–Vazirani oracle function for secret string `s`:
    `f(x) = s · x` (mod 2). -/
def bvFun (n : ℕ) (s : Fin (2 ^ n)) : Fin (2 ^ n) → Bool :=
  fun x => bdot_BV s.val x.val

/-- For the BV oracle, the phase factor `(-1)^{f(x)}` is exactly `(-1)^{s·x}`. -/
theorem bvFun_phase (n : ℕ) (s : Fin (2 ^ n)) (x : Fin (2 ^ n)) :
    (if bvFun n s x then (-1 : ℂ) else 1) = dotSign s.val x.val := by
  simp [bvFun, dotSign]

/-
The BV amplitude for the BV oracle: it is `2^n` at `y = s` and `0` otherwise.
-/
theorem bvAmp_bvFun (n : ℕ) (s y : Fin (2 ^ n)) :
    bvAmp n (bvFun n s) y = if y = s then (2 ^ n : ℂ) else 0 := by
  -- By definition of `bvAmp`, we can rewrite the sum using `bvFun_phase`.
  have h_sum : ∑ x : Fin (2 ^ n), dotSign y.val x.val * (if bvFun n s x then (-1 : ℂ) else 1) = ∑ x : Fin (2 ^ n), dotSign y.val x.val * dotSign s.val x.val := by
    exact Finset.sum_congr rfl fun x hx => by rw [ bvFun_phase ] ;
  -- By `dotSign_mul`, `dotSign y.val x.val * dotSign s.val x.val = dotSign (y.val ^^^ s.val) x.val`.
  have h_dot_sign_mul : ∑ x : Fin (2 ^ n), dotSign y.val x.val * dotSign s.val x.val = ∑ x : Fin (2 ^ n), dotSign (y.val ^^^ s.val) x.val := by
    exact Finset.sum_congr rfl fun _ _ => dotSign_mul _ _ _ ▸ rfl
  simp_all +decide [ bvAmp ];
  convert dotSign_char_sum n ( y.val ^^^ s.val ) ( Nat.xor_lt_two_pow ( Fin.is_lt y ) ( Fin.is_lt s ) ) using 1;
  simp +decide [ Fin.ext_iff, Nat.xor_eq_zero_iff ]


/-! ## Correctness -/

theorem BV_correct (n : ℕ) (s : Fin (2 ^ n)) :
    (stdBra s ⊗ bra1) * DJ_output n (bvFun n s) = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [ BV_amplitude, bvAmp_bvFun ] ; norm_num

/-
For any string `y ≠ s` the output amplitude vanishes: the algorithm is
    deterministic.
-/
theorem BV_orthogonal (n : ℕ) (s y : Fin (2 ^ n)) (hy : y ≠ s) :
    (stdBra y ⊗ bra1) * DJ_output n (bvFun n s) = 0 := by
  rw [ BV_amplitude, bvAmp_bvFun ] ; aesop

/-- The measurement probability (amplitude squared) at `|s⟩` equals `1`. -/
theorem BV_prob_one (n : ℕ) (s : Fin (2 ^ n)) :
    ((stdBra s ⊗ bra1) * DJ_output n (bvFun n s)) ^ 2 = 1 := by
  rw [BV_correct]; simp

end DiracRepr
end
