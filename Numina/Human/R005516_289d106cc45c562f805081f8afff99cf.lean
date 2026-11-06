import Mathlib

/-Daniel wrote all the positive integers from 1 to $n$ inclusive on a piece of paper. After careful observation, he realized that the sum of all the digits that he wrote was exactly 10,000 . Find $n$.-/
theorem number_theory_608587 (n : ℕ) (hn : n ≥ 1)
  (h : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).sum = 10000) :
  n = 799 := by

  -- Let f(x) = ∑_(n=0)^x (sum of digits of x)
  let f : ℕ → ℕ := fun n ↦ ∑ i ∈ Finset.Icc 0 n, (Nat.digits 10 i).sum

  -- We may add n = 0 because the sum of digits of 0 is 0
  have h_f_eq (n : ℕ) :
    f n = ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).sum := by
      unfold f
      rw [← Finset.add_sum_Ioc_eq_sum_Icc (show n ≥ 0 by exact Nat.zero_le n)]
      norm_num
      rfl

  -- so the condition becomes f n = 10000
  have h' : f n = 10000 := by
    trans ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).sum
    exact h_f_eq n
    exact h

  -- we show that f is strictly monotone
  have h_f_monotone : StrictMono f := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    unfold f
    rw [Finset.sum_Icc_succ_top (show n + 1 ≥ 0 by apply Nat.zero_le)]
    refine Nat.lt_add_of_pos_right ?_
    refine Nat.sum_pos_iff_exists_pos.mpr ?_

    have hdigits : (Nat.digits 10 (n + 1)) ≠ [] := by
      apply Nat.digits_ne_nil_iff_ne_zero.mpr
      exact Ne.symm (Nat.zero_ne_add_one n)

    use (Nat.digits 10 (n + 1)).getLast hdigits
    constructor
    exact List.getLast_mem hdigits
    refine Nat.zero_lt_of_ne_zero ?_
    refine Nat.getLast_digit_ne_zero 10 ?_
    exact Ne.symm (Nat.zero_ne_add_one n)

  -- thus f is injective
  have h_f_inj : Function.Injective f := by
    exact StrictMono.injective h_f_monotone

  -- Observe that:
  --  f(99)= \sum_{a=0}^{9} \sum_{b=0}^{9} (a+b)
  have f_99_rw : f 99 = ∑ a ∈ Finset.Icc 0 9, ∑ b ∈ Finset.Icc 0 9,
    (Nat.digits 10 (10 * a + b)).sum := by
      unfold f
      rw [← Finset.sum_product']
      let i : (ℕ × ℕ) → ℕ := fun ⟨a, b⟩ ↦ 10 * a + b
      let j : ℕ → (ℕ × ℕ) := fun n ↦ ⟨n / 10, n % 10⟩
      apply Finset.sum_nbij' j i
      · intro n n_mem
        apply Finset.mem_Icc.mp at n_mem
        simp [j]
        constructor
        · apply Nat.div_le_iff_le_mul_add_pred ?_ |>.mpr
          norm_num
          exact n_mem.2
          norm_num
        · suffices h : n % 10 < 10 by linarith only [h]
          apply Nat.mod_lt
          norm_num
      · intro ⟨a, b⟩ abmem
        simp at abmem
        simp [i]
        linarith only [abmem]
      · intro n n_mem
        apply Finset.mem_Icc.mp at n_mem
        simp [i, j]
        exact Nat.div_add_mod n 10
      · intro ⟨a, b⟩ abmem
        simp at abmem
        simp [i, j]
        constructor
        · refine Nat.div_eq_of_lt_le ?_ ?_
          linarith
          linarith
        · refine Nat.mod_eq_of_modEq ?_ ?_
          refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_)
          simp
          linarith
      · intro n n_mem
        apply Finset.mem_Icc.mp at n_mem
        simp [i, j]
        congr
        symm
        exact Nat.div_add_mod n 10

  -- ... = 10 \sum_{b=0}^{9} b+10 \sum_{a=0}^{9} a = 900
  have h_f_99 : f 99 = 900 := by
    rw [f_99_rw]

    have lem_digits_10_a_b (a b : ℕ) (ha : a ∈ Finset.Icc 0 9) (hb : b ∈ Finset.Icc 0 9) :
      (Nat.digits 10 (10 * a + b)).sum = a + b := by
        have hb_lt : b < 10 := by linarith [Finset.mem_Icc.mp hb |>.2]
        have ha_lt : a < 10 := by linarith [Finset.mem_Icc.mp ha |>.2]
        by_cases ha0 : a = 0
        · rw [ha0]
          by_cases hb0 : b = 0
          · simp [hb0]
          simp [hb_lt, hb0]

        rw [add_comm, Nat.digits_add]
        simp [ha_lt, ha0]
        ring
        norm_num
        exact hb_lt
        right; exact ha0

    have : ∑ a ∈ Finset.Icc 0 9, ∑ b ∈ Finset.Icc 0 9, (Nat.digits 10 (10 * a + b)).sum =
      ∑ a ∈ Finset.Icc 0 9, ∑ b ∈ Finset.Icc 0 9, (a + b) := by
        apply Finset.sum_congr
        rfl
        intro a ha

        apply Finset.sum_congr
        rfl
        intro b hb

        exact lem_digits_10_a_b a b ha hb
    rw [this]

    have : ∑ a ∈ Finset.Icc 0 9, ∑ b ∈ Finset.Icc 0 9, (a + b) =
      ∑ a ∈ Finset.Icc 0 9, (10 * a + ∑ b ∈ Finset.Icc 0 9, b) := by
        apply Finset.sum_congr
        rfl
        intro a ha

        rw [Finset.sum_add_distrib]
        simp
    rw [this]

    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp

    have : ∑ i ∈ Finset.Icc 0 9, i = 45 := by
      rw [Finset.sum_Icc_succ_top (show 8 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 7 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 6 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 5 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 4 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 3 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 2 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 1 + 1 ≥ 0 by norm_num)]
      rw [Finset.sum_Icc_succ_top (show 0 + 1 ≥ 0 by norm_num)]
      simp

    rw [this]
    rfl

  -- If $a$ is an integer between 1 and 9 inclusive, and 0 ≤ x < 100, then:
  -- sum of digits of 100 * a + x = a + sum of digits of x
  have h_sum_100a_x (a x : ℕ) (ha : a ∈ Finset.Icc 0 9) (hx : x ∈ Finset.Ico 0 100) :
    (Nat.digits 10 (100 * a + x)).sum = a + (Nat.digits 10 (x)).sum := by

      let b := x / 10
      let c := x % 10

      have hb_lt : b < 10 := by
        unfold b
        refine Nat.div_lt_of_lt_mul ?_
        norm_num
        exact Finset.mem_Ico.mp hx |>.2

      have hx_eq : x = 10 * b + c := by
        unfold b c
        exact Eq.symm (Nat.div_add_mod x 10)

      have h_dig_x : (Nat.digits 10 (x)).sum = b + c := by
        rw [hx_eq]
        by_cases hb0 : b = 0
        · by_cases hc0 : c = 0
          · rw [hb0, hc0]
            simp
          rw [add_comm, Nat.digits_add]
          rw [hb0]
          simp
          norm_num
          refine Nat.mod_lt x ?_
          norm_num
          left
          exact hc0
        rw [add_comm, Nat.digits_add]
        simp [hb0, hb_lt]
        ring
        norm_num
        unfold c
        refine Nat.mod_lt x ?_
        norm_num
        right
        exact hb0
      rw [h_dig_x]

      by_cases ha0 : a = 0
      · simp [ha0, h_dig_x]

      by_cases hb0 : b = 0
      · have : x = c := by rw [hx_eq, hb0]; ring
        rw [this, hb0]
        norm_num
        by_cases hc0 : c = 0
        · simp [hc0]
          rw [show 100 = 10 ^ 2 by norm_num]
          by_cases ha0 : a = 0
          · simp [ha0]
          rw [Nat.digits_base_pow_mul]
          rw [Nat.digits_of_lt]
          simp
          exact ha0
          linarith only [Finset.mem_Icc.mp ha]
          norm_num
          exact Nat.zero_lt_of_ne_zero ha0

        have : Nat.digits 10 c = [c] := by
          refine Nat.digits_of_lt 10 c hc0 ?_
          refine Nat.mod_lt x ?_
          norm_num
        rw [show 100 = 10 * 10 by norm_num, mul_assoc, add_comm]
        rw [Nat.digits_add 10 (by norm_num)]
        simp
        rw [show 10 * a = 0 + 10 * a by norm_num]
        rw [Nat.digits_add 10 (by norm_num)]
        simp [ha0, show a < 10 by linarith only [Finset.mem_Icc.mp ha]]
        ring
        norm_num
        right; exact ha0
        exact Nat.mod_lt x (by norm_num)
        left
        exact hc0

      have : (Nat.digits 10 x).length = 2 := by
        rw [hx_eq, add_comm, Nat.digits_add]
        simp [hb0, hb_lt]
        norm_num
        exact Nat.mod_lt x (by norm_num)
        right; exact hb0

      rw [show 100 = 10 ^ 2 by norm_num, ← this, add_comm]
      rw [← Nat.digits_append_digits, List.sum_append, h_dig_x]
      simp [ha0, show a < 10 by linarith only [Finset.mem_Icc.mp ha]]
      ring
      norm_num

  -- using the above fact, we have
  -- \sum_{n=100 a}^{100 a+99} S(n) = \sum_{n=100 a}^{100 a+99} (a + S(n - 100 a)) = 100 a + f(99) = 100 a + 900
  have h_sum_digits_100a_up_100 (a : ℕ) (ha : a ∈ Finset.Icc 0 9) :
    ∑ i ∈ Finset.Ico (100 * a) (100 * a + 100), (Nat.digits 10 i).sum = 100 * a + f 99 := by
      nth_rw 1 [show 100 * a = 0 + 100 * a by ring]
      nth_rw 1 [show 100 * a + 100 = 100 + 100 * a by ring]
      rw [← Finset.sum_Ico_add]

      have : ∑ x ∈ Finset.Ico 0 100, (Nat.digits 10 (100 * a + x)).sum =
        ∑ x ∈ Finset.Ico 0 100, (a + (Nat.digits 10 x).sum) := by
        apply Finset.sum_congr
        rfl
        intro x xmem
        exact h_sum_100a_x a x ha xmem

      rw [this, Finset.sum_add_distrib]
      simp [f]
      rfl

  -- Summing, we get:
  -- f(100 a + 99) = \sum_{n=0}^{a} (100 a + 900) = 900(a + 1) + 50 a (a + 1)
  have hf_100a_99 (a : ℕ) (ha : a ∈ Finset.Icc 0 9) :
    f (100 * a + 99) = 900 * (a + 1) + 50 * a * (a + 1) := by
      induction' a with a ih
      · simp [h_f_99]
      · have : f (100 * (a + 1) + 99) = f (100 * a + 99) + ∑ i ∈ Finset.Ico (100 * (a + 1)) (100 * (a + 1) + 100), (Nat.digits 10 i).sum := by
          simp [f]
          rw [show Finset.Icc 0 (100 * a + 99) = Finset.Ico 0 (100 * a + 100) by rfl]
          rw [show 100 * (a + 1) = 100 * a + 100 by ring]
          rw [Finset.sum_Ico_consecutive]
          rfl
          apply Nat.zero_le
          linarith
        rw [this, ih, h_sum_digits_100a_up_100, h_f_99]
        ring
        exact ha
        apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.zero_le a
        linarith [Finset.mem_Icc.mp ha]

  -- Therefore $f(799)=10000$, and our answer is 799 .
  have hf_799 : f 799 = 10000 := by
    rw [show 799 = 100 * 7 + 99 by norm_num]
    rw [hf_100a_99]
    norm_num

  apply h_f_inj
  trans 10000
  · exact h'
  · exact hf_799.symm
