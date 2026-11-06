import Mathlib
open Real Nat 
noncomputable section

-- Define the Fibonacci sequence.
def F : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

-- Lemma: Prove $a_n = F_(n+1) * F_(n+3) - F_n * F_(n+4) = (-1)^n * 2$.
lemma a_n_recurrence (n : ℕ) (hn : n ≥ 1) :
    (F (n + 1) * F (n + 3) - F n * F (n + 4) : ℤ) = (-1 : ℤ) ^ n * 2 := by
  induction n with
  | zero =>
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      have h_f1 : F 1 = 1 := rfl
      have h_f2 : F 2 = 1 := rfl
      have h_f3 : F 3 = F 2 + F 1 := rfl
      have h_f3_val : F 3 = 2 := by simp [F]
      have h_f4 : F 4 = F 3 + F 2 := rfl
      have h_f4_val : F 4 = 3 := by simp [F]
      have h_f5 : F 5 = F 4 + F 3 := rfl
      have h_f5_val : F 5 = 5 := by simp [F]
      have h_a1 : (F 2 * F 4 - F 1 * F 5 : ℤ) = 1 * 3 - 1 * 5 := by rw [h_f2, h_f4_val, h_f1, h_f5_val]; norm_num
      have h_a1_val : 1 * 3 - 1 * 5 = -2 := by norm_num
      have h_target : (-1 : ℤ) ^ 1 * 2 = -2 := by norm_num
      exact h_a1_val.trans h_target
    | succ n =>
      -- Induction step: Prove $a_(n+2) = -a_(n+1)$.
      have h_a_n2 : (F (n + 3) * F (n + 5) - F (n + 2) * F (n + 6) : ℤ) =
                    F (n + 3) * F (n + 5) - F (n + 2) * (F (n + 5) + F (n + 4)) := by
        have h_f6 : F (n + 6) = F (n + 5) + F (n + 4) := by rw [F, Nat.add_assoc]
        rw [h_f6]; rfl
      have h_expand : (F (n + 3) * F (n + 5) - F (n + 2) * (F (n + 5) + F (n + 4)) : ℤ) =
                      (F (n + 3) - F (n + 2)) * F (n + 5) - F (n + 2) * F (n + 4) := by
        conv =>
          lhs; rw [mul_add, ← Int.sub_sub]
        conv =>
          rhs; rw [Int.sub_mul]
      have h_f_n3 : F (n + 3) = F (n + 2) + F (n + 1) := by rw [F, Nat.add_assoc]
      have h_diff : F (n + 3) - F (n + 2) = F (n + 1) := by omega
      have h_a_n2_val : ((F (n + 3) - F (n + 2)) * F (n + 5) - F (n + 2) * F (n + 4) : ℤ) =
                        (F (n + 1) * F (n + 5) - F (n + 2) * F (n + 4) : ℤ) := by
        have h_diff_int : (F (n + 3) : ℤ) - (F (n + 2) : ℤ) = (F (n + 1) : ℤ) := by omega
        rw [h_diff_int]
      have h_a_n1 : F (n + 2) * F (n + 4) - F (n + 1) * F (n + 5) = (-1 : ℤ) ^ (n + 1) * 2 := ih (by linarith)
      have h_neg_a_n1 : -(F (n + 2) * F (n + 4) - F (n + 1) * F (n + 5)) = -((-1 : ℤ) ^ (n + 1) * 2) := by
        rw [h_a_n1]
      have h_a_n2_eq : (F (n + 1) * F (n + 5) - F (n + 2) * F (n + 4) : ℤ) =
                       (-(F (n + 2) * F (n + 4) - F (n + 1) * F (n + 5)) : ℤ) := by
        ring
      have h_target_n2 : (-1 : ℤ) ^ (n + 2) * 2 = -((-1 : ℤ) ^ (n + 1) * 2) := by
        rw [pow_succ]; ring
      have h_a_n2_final : (F (n + 1) * F (n + 5) - F (n + 2) * F (n + 4) : ℤ) = (-1 : ℤ) ^ (n + 2) * 2 := by
        rw [h_a_n2_eq, h_neg_a_n1, h_target_n2]
      have h_a_n2_rewrite : (F (n + 3) * F (n + 5) - F (n + 2) * F (n + 6) : ℤ) =
                            (F (n + 1) * F (n + 5) - F (n + 2) * F (n + 4) : ℤ) := by
        rw [h_a_n2, h_expand, h_a_n2_val]
      exact h_a_n2_rewrite.trans h_a_n2_final

/-1. Let the sequence $\left\{F_{n}\right\}$ satisfy the recursive relation $F_{1}=F_{2}=4, F_{n+2}=F_{n+1}+F_{n}, n=1,2, \cdots$ Prove: For any natural number $n$, a right-angled triangle can be formed with side lengths $F_{n} \cdot F_{n+4}, F_{n+1} \cdot F_{n+3}, 2 F_{n+2}$.-/
theorem number_theory_6045678 (n : ℕ) (hn : n ≥ 1) :
    (-1 : ℤ) ^ n * (2 * F (n + 2))^2 = (F (n + 1) * F (n + 3))^2 - (F n * F (n + 4))^2 := by
  -- Prove $2 * F_(n+2)^2 = F_(n+1) F_(n+3) + F_n F_(n+4)$.
  have h_square : (2 * F (n + 2))^2 = 2 * F (n + 2) * (F (n + 3) + F n) := by
    simp [F]; ring
  have h_distrib : F (n + 2) * (F (n + 3) + F n) = F (n + 2) * F (n + 3) + F (n + 2) * F n := by
    rw [mul_add]
  have h_rewrite : F (n + 2) * F (n + 3) + F (n + 2) * F n = F (n + 1) * F (n + 3) + F n * F (n + 4) := by
    simp [F]; ring
  have h_interim : (2 * F (n + 2))^2 = 2 * (F (n + 1) * F (n + 3) + F n * F (n + 4)) := by
    rw [h_square, mul_assoc, h_distrib, h_rewrite]
  have h_adjust : 2 * (F (n + 2))^2 = (F (n + 1) * F (n + 3) + F n * F (n + 4)) := by linarith
  have h_adjust_int : (2 * (F (n + 2))^2 : ℤ) = (F (n + 1) * F (n + 3) + F n * F (n + 4) : ℤ) := by exact_mod_cast h_adjust
  -- Use lemma to prove $F_(n+1) F_(n+3) - F_n F_(n+4) = (-1)^n * 2$.
  have h_a_n : (F (n + 1) * F (n + 3) - F n * F (n + 4) : ℤ) = (-1 : ℤ) ^ n * 2 := by
    apply a_n_recurrence n hn
  have h_a_n_int : (↑(F (n + 1)) * ↑(F (n + 3)) - ↑(F n) * ↑(F (n + 4)) : ℤ) = (-1 : ℤ) ^ n * 2 := by omega
  -- Derive target equation.
  have h_product : (-1 : ℤ) ^ n * 2 * 2 * (F (n + 2))^2 = (F (n + 1) * F (n + 3) - F n * F (n + 4)) * (F (n + 1) * F (n + 3) + F n * F (n + 4)) := by
    rw [mul_assoc, h_adjust_int, ← h_a_n_int]
  have h_product_simp : (-1 : ℤ) ^ n * 2 * 2 * (F (n + 2))^2 = (-1 : ℤ) ^ n * (2 * F (n + 2))^2 := by linarith
  have h_diff_sq : (F (n + 1) * F (n + 3))^2 - (F n * F (n + 4))^2 = (F (n + 1) * F (n + 3) - F n * F (n + 4)) * (F (n + 1) * F (n + 3) + F n * F (n + 4)) := by
    rw [sq_sub_sq, mul_comm]
  have h_diff_sq_int : ((F (n + 1) * F (n + 3))^2 - (F n * F (n + 4))^2 : ℤ) = (F (n + 1) * F (n + 3) - F n * F (n + 4)) * (F (n + 1) * F (n + 3) + F n * F (n + 4)) := by linarith
  -- Combine results.
  have h_result : (-1 : ℤ) ^ n * (2 * F (n + 2))^2 = (F (n + 1) * F (n + 3))^2 - (F n * F (n + 4))^2 := by
    conv =>
      lhs; rw [← h_product_simp]
    conv =>
      rhs; rw [h_diff_sq_int]
    exact h_product
  exact h_result
