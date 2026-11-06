import Mathlib

open Real

/- At a competition with $N$ players, the number of players given elite status is equal to $2^{1+\lfloor \log_{2} (N-1) \rfloor}-N$. Suppose that $19$ players are given elite status. What is the sum of the two smallest possible values of $N$?
$\textbf{(A)}\ 38 \qquad \textbf{(B)}\ 90 \qquad \textbf{(C)}\ 154 \qquad \textbf{(D)}\ 406 \qquad \textbf{(E)}\ 1024$ -/
theorem number_theory_94593
    (S : Set ℕ) (hS : S = {N : ℕ | 2^(1 + ⌊logb 2 (N - 1)⌋₊) - (N : ℝ) = 19}) :
    Nat.nth S 0 + Nat.nth S 1 = 154 := by classical
  -- We define S to be the of positive integers such that 2^(1 + ⌊log_2(N - 1)⌋) - N = 19
  -- To begin, we rearrange the relation to get 2^⌊log_2(N - 1)⌋ = (N + 19) / 2
  have h₁ (N : ℕ) : N ∈ S ↔ ⌊logb 2 (N - 1)⌋₊ = logb 2 ((N + 19) / 2) := by
    rw [hS, Set.mem_setOf]
    constructor <;> intro hN
    · rw [sub_eq_iff_eq_add', pow_add, pow_one, mul_comm, ← eq_div_iff_mul_eq two_ne_zero] at hN
      rw [← hN, logb_pow, logb_self_eq_one one_lt_two, mul_one]
    · apply_fun fun n ↦ (2 : ℝ) ^ (1 + n) - N at hN
      convert hN
      · norm_cast
      · rw [rpow_add zero_lt_two, rpow_one, eq_sub_iff_add_eq', rpow_logb, mul_div_cancel₀]
        all_goals norm_num
        positivity

  -- Since ⌊⬝⌋ is an integer, we have N = 2^(m + 1) - 19
  have h₂ (N : ℕ) (hN : N ∈ S) : ∃ m, N = 2 ^ (m + 1) - 19 := by
    rw [h₁] at hN
    apply_fun fun n ↦ (2 : ℝ) ^ n at hN
    rw [rpow_logb, eq_div_iff_mul_eq, ← sub_eq_iff_eq_add, rpow_natCast] at hN
    · simp_rw [pow_add, pow_one]
      use ⌊logb 2 (N - 1 : ℝ)⌋₊
      rify
      nth_rw 1 [← hN]
      rw [Nat.cast_sub, Nat.cast_mul, Nat.cast_pow, Nat.cast_two, Nat.cast_ofNat]
      have : 0 ≤ (N : ℝ) := Nat.cast_nonneg' N
      rw [← hN, sub_nonneg] at this
      exact_mod_cast this
    all_goals norm_num
    positivity

  -- Moreover, as N > 0, we have m ≥ 5
  have h₃ (N : ℕ) (hN : N ∈ S) : ∃ m, N = 2 ^ (m + 1) - 19 ∧ m ≥ 5 := by
    obtain ⟨m, hm⟩ := h₂ N hN
    use m, hm
    by_contra! hm'
    replace h₁ := (h₁ N).mp hN
    have : N ≠ 0 := by
      rintro rfl
      simp at h₁
      rw [eq_comm, logb_eq_zero] at h₁
      norm_num at h₁
    have : m ≤ 3 ∨ m = 4 := by omega
    rcases this with hm' | rfl | rfl | rfl | rfl
    · have : N = 0 := by
        rw [hm, tsub_eq_zero_iff_le]
        exact (Nat.pow_le_pow_right zero_lt_two <| Nat.add_le_add_right hm' 1).trans (by decide)
      tauto
    · norm_num at hm
      subst hm
      norm_num at h₁
      have h : ⌊logb 2 12⌋₊ = 3 := by
        rw [Nat.floor_eq_iff, logb_lt_iff_lt_rpow, le_logb_iff_rpow_le] <;> norm_num
        apply logb_nonneg <;> norm_num
      have h' : logb 2 16 = 4 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      rw [h, h'] at h₁
      norm_num at h₁

  -- Now, we compute the minimum positive integer in S
  -- We begin by showing that 2^6 - 19 = 45 ∈ S by verifying the relation
  have hS_45 : 45 ∈ S := by
    rw [h₁]
    norm_num
    have h : ⌊logb 2 44⌋₊ = 5 := by
      rw [Nat.floor_eq_iff, logb_lt_iff_lt_rpow, le_logb_iff_rpow_le] <;> norm_num
      apply logb_nonneg <;> norm_num
    have h' : logb 2 32 = 5 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h, h']
    norm_cast
  -- As N ∈ S ↔ N = 2^(m + 1) - 19 and m ≥ 5, 45 must be the minimum number
  have h_nth_0 : Nat.nth S 0 = 45 := by
    have : ∃ n, S n := ⟨45, hS_45⟩
    rw [Nat.nth_zero_of_exists this, Nat.find_eq_iff]
    use hS_45, fun n hn ↦ ?_
    intro hn'
    obtain ⟨m, rfl, hm⟩ := h₃ n hn'
    have : 2 ^ (m + 1) < 2 ^ 6 := by omega
    rw [Nat.pow_lt_pow_iff_right one_lt_two] at this
    omega

  -- Next, 2^7 - 19 = 109 ∈ S as well
  have hS_109 : 109 ∈ S := by
    rw [h₁]
    norm_num
    have h : ⌊logb 2 108⌋₊ = 6 := by
      rw [Nat.floor_eq_iff, logb_lt_iff_lt_rpow, le_logb_iff_rpow_le] <;> norm_num
      apply logb_nonneg <;> norm_num
    have h' : logb 2 64 = 6 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h, h']
    norm_cast
  -- As m = 6 is the next candidate to m = 5, 109 must be the second smallest number
  have h_nth_1 : Nat.nth S 1 = 109 := by
    rw [Nat.nth_eq_sInf]
    simp_rw [Nat.lt_one_iff, forall_eq, h_nth_0]
    have : {n | S n ∧ 45 < n}.Nonempty := by use 109, hS_109, by decide
    rw [Nat.sInf_def this]
    convert (Nat.find_eq_iff this).mpr ⟨⟨hS_109, by decide⟩, ?_⟩
    intro n hn ⟨hn', hn''⟩
    obtain ⟨m, rfl, hm⟩ := h₃ n hn'
    have : 2 ^ (m + 1) < 2 ^ 7 := by omega
    rw [Nat.pow_lt_pow_iff_right one_lt_two] at this
    have : m = 5 := by omega
    subst this
    norm_num at hn''

  -- Hence, the desired answer is 45 + 109 = 154
  rw [h_nth_0, h_nth_1]