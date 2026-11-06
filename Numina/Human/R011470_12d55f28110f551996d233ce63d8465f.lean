import Mathlib
set_option maxHeartbeats 999999999
/- Find the number of positive integers less than $1000$ that can be expressed as the difference of two integral powers of $2.$ -/
theorem number_theory_42724 :
  Set.ncard {n : ℕ | ∃ a b, n = 2 ^ a - 2 ^ b ∧ a ≥ b ∧ n < 1000 ∧ 0 < n} = 50 := by
  have en : {n : ℕ | ∃ a b, n = 2 ^ a - 2 ^ b ∧ a ≥ b ∧ n < 1000 ∧ 0 < n} = {1, 2, 3, 4, 6, 7, 8, 12, 14, 15, 16, 24, 28, 30, 31, 32, 48, 56, 60, 62, 63, 64, 96, 112, 120, 124, 126, 127, 128, 192, 224, 240, 248, 252, 254, 255, 256, 384, 448, 480, 496, 504, 508, 510, 511, 512, 768, 896, 960, 992} := by
    ext n
    simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    symm
    constructor <;> intro h
    -- all listed numbers satisfy the conditions
    · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := h
      exists 1, 0; exists 2, 1; exists 2, 0; exists 3, 2; exists 3, 1; exists 3, 0; exists 4, 3; exists 4, 2; exists 4, 1; exists 4, 0; exists 5, 4; exists 5, 3; exists 5, 2; exists 5, 1; exists 5, 0; exists 6, 5; exists 6, 4; exists 6, 3; exists 6, 2; exists 6, 1; exists 6, 0; exists 7, 6; exists 7, 5; exists 7, 4; exists 7, 3; exists 7, 2; exists 7, 1; exists 7, 0; exists 8, 7; exists 8, 6; exists 8, 5; exists 8, 4; exists 8, 3; exists 8, 2; exists 8, 1; exists 8, 0; exists 9, 8; exists 9, 7; exists 9, 6; exists 9, 5; exists 9, 4; exists 9, 3; exists 9, 2; exists 9, 1; exists 9, 0; exists 10, 9; exists 10, 8; exists 10, 7; exists 10, 6; exists 10, 5
    -- solve
    · obtain ⟨a, b, h1, h2, h3, h4⟩ := h
      obtain ⟨w, h⟩: ∃ w, w = a - b := ⟨_, rfl⟩
      have aj : a = b + w := by omega
      subst a; clear h h2
      -- now we do cases on b
      -- it is important to establish an upper bound on b by establishing an upper bound on 2^b
      rw [Nat.pow_add, ← Nat.mul_sub_one] at h1
      have js : 2^w - 1 ≥ 1 := by
        cases w with
        | zero => norm_num at h1; linarith
        | succ w =>
          simp only [Nat.pow_succ, ge_iff_le]
          clear * -
          have aj : 1 ≤ 2^w := by exact Nat.one_le_two_pow
          omega
      have jw : 2^b ≤ 1024 := by
        apply Nat.mul_le_mul_left (2^b) at js
        linarith
      rify at jw
      rw [(by norm_num : (1024 : ℝ) = (2 : ℝ)^(10 : ℝ)), (by norm_num : (2 : ℝ)^b = (2 : ℝ)^(↑b : ℝ))] at jw
      apply Real.logb_le_logb_of_le (b := 2) (by norm_num) (by {have := @Nat.one_le_two_pow b; norm_cast}) at jw
      rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)] at jw
      norm_cast at jw -- now we've established a bound on b
      have ew (a b : ℕ) (h : 2^a ≤ 2^b) : a ≤ b := by
        rify at h
        rw [(by norm_num : (2 : ℝ)^a = (2 : ℝ)^(↑a : ℝ)), (by norm_num : (2 : ℝ)^b = (2 : ℝ)^(↑b : ℝ))] at h
        apply Real.logb_le_logb_of_le (b := 2) (by norm_num) (by {have := @Nat.one_le_two_pow a; norm_cast}) at h
        rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)] at h
        exact_mod_cast h
      (obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by clear * - jw; omega)
      -- establish upper bounds on w
      have wk : 2^w ≤ 2^10 := by omega
      pick_goal 2
      have wk : 2^w ≤ 2^9 := by omega
      pick_goal 3
      have wk : 2^w ≤ 2^8 := by omega
      pick_goal 4
      have wk : 2^w ≤ 2^7 := by omega
      pick_goal 5
      have wk : 2^w ≤ 2^6 := by omega
      pick_goal 6
      have wk : 2^w ≤ 2^6 := by omega
      pick_goal 7
      have wk : 2^w ≤ 2^5 := by omega
      pick_goal 8
      have wk : 2^w ≤ 2^4 := by omega
      pick_goal 9
      have wk : 2^w ≤ 2^3 := by omega
      pick_goal 10
      have wk : 2^w ≤ 2^2 := by omega
      pick_goal 11
      apply Nat.mul_le_mul_left (2^10) at js
      linarith
      all_goals have de := ew _ _ wk
      -- now we do interval_cases
      all_goals interval_cases w
      all_goals subst n
      all_goals norm_num at js h3 h4
      -- now we calculate
      · simp only [(by decide : (2^9 * (2^1 - 1) = 512) ↔ True), or_true, true_or]
      · simp only [(by decide : (2^8 * (2^1 - 1) = 256) ↔ True), or_true, true_or]
      · simp only [(by decide : (2^8 * (2^2 - 1) = 768) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 7 * (2 ^ 1 - 1) = 128) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 7 * (2 ^ 2 - 1) = 384) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 7 * (2 ^ 3 - 1) = 896) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 6 * (2 ^ 1 - 1) = 64) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 6 * (2 ^ 2 - 1) = 192) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 6 * (2 ^ 3 - 1) = 448) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 6 * (2 ^ 4 - 1) = 960) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 5 * (2 ^ 1 - 1) = 32) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 5 * (2 ^ 2 - 1) = 96) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 5 * (2 ^ 3 - 1) = 224) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 5 * (2 ^ 4 - 1) = 480) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 5 * (2 ^ 5 - 1) = 992) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 4 * (2 ^ 1 - 1) = 16) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 4 * (2 ^ 2 - 1) = 48) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 4 * (2 ^ 3 - 1) = 112) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 4 * (2 ^ 4 - 1) = 240) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 4 * (2 ^ 5 - 1) = 496) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 3 * (2 ^ 1 - 1) = 8) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 3 * (2 ^ 2 - 1) = 24) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 3 * (2 ^ 3 - 1) = 56) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 3 * (2 ^ 4 - 1) = 120) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 3 * (2 ^ 5 - 1) = 248) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 3 * (2 ^ 6 - 1) = 504) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 1 - 1) = 4) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 2 - 1) = 12) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 3 - 1) = 28) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 4 - 1) = 60) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 5 - 1) = 124) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 6 - 1) = 252) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 2 * (2 ^ 7 - 1) = 508) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 1 - 1) = 2) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 2 - 1) = 6) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 3 - 1) = 14) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 4 - 1) = 30) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 5 - 1) = 62) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 6 - 1) = 126) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 7 - 1) = 254) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 1 * (2 ^ 8 - 1) = 510) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 1 - 1) = 1) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 2 - 1) = 3) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 3 - 1) = 7) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 4 - 1) = 15) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 5 - 1) = 31) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 6 - 1) = 63) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 7 - 1) = 127) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 8 - 1) = 255) ↔ True), or_true, true_or]
      · simp only [(by decide : (2 ^ 0 * (2 ^ 9 - 1) = 511) ↔ True), or_true, true_or]
  rw [en]
  (repeat rw [Set.ncard_insert_of_not_mem]) <;> try decide
  rw [Set.ncard_singleton]