import Mathlib

open Real Set
open scoped BigOperators

/- Let $n \geqslant 0$ be an integer, and let $a_{0}, a_{1}, \ldots, a_{n}$ be real numbers. Show that there exists $k \in\{0,1, \ldots, n\}$ such that

$$
a_{0}+a_{1} x+a_{2} x^{2}+\cdots+a_{n} x^{n} \leqslant a_{0}+a_{1}+\cdots+a_{k}
$$

for all real numbers $x \in[0,1]$.

# -/
theorem inequalities_606431 {n : ℕ} (a : ℕ → ℝ) :
  ∃ k ∈ Finset.Icc 0 n, ∀ x ∈ Icc 0 1, ∑ i ∈ Finset.range (n + 1), a i * x ^ i ≤ ∑ i ∈ Finset.range (k + 1), a i := by

    -- prove by induction on n
    induction n generalizing a
    case zero => simp_all -- when n = 0 there is nothing to prove
    case succ n ih =>
      -- suppose the theorem holds for n, we prove it for n + 1

      -- first we need a lemma that a + b * x ≤ max a (a + b) for all x ∈ [0, 1]
      have lem {a b x : ℝ} (hx : x ∈ Icc 0 1) : a + b * x ≤ max a (a + b) := by
        have ⟨x_ge, x_le⟩ := hx
        -- we divide into cases whether b < 0 or b ≥ 0
        by_cases h : b < 0
        · -- in case b < 0, we have a + b * x ≤ a
          have : a + b * x ≤ a := by
            have : b * x ≤ 0 := by
              apply mul_nonpos_iff.mpr
              right; constructor <;> linarith
            linarith
          exact le_max_of_le_left this
        · -- in case b ≥ 0, we have a + b * x ≤ a + b as x ≤ 1
          have : b * x ≤ b := by
            nth_rw 2 [show b = b * 1 by ring]
            apply mul_le_mul
            all_goals linarith
          have : a + b * x ≤ a + b := by
            apply add_le_add_left
            exact this
          trans a + b
          assumption
          exact le_max_right a (a + b)

      -- define an auxiliary sequence a' for sake of induction, where a' i := a (i + 1)
      let a' : ℕ → ℝ := fun i ↦ a (i + 1)
      -- let k be given by induction hypothesis applied to a'
      have ⟨k, ⟨k_mem, hk⟩⟩ := ih a'
      rw [Finset.mem_Icc] at k_mem

      -- we show that ∑ i ∈ Finset.range (n + 2), a i * x ^ i is equal to
      -- a 0 + x * ∑ i ∈ Finset.range (n + 1), a' i * x ^ i
      have h_sum_succ (x : ℝ) : ∑ i ∈ Finset.range (n + 1 + 1), a i * x ^ i =
        a 0 + x * ∑ i ∈ Finset.range (n + 1), a' i * x ^ i := by
          rw [Finset.range_eq_Ico]
          rw [Finset.sum_eq_sum_Ico_succ_bot] -- take out the first summand from lhs
          rw [show x ^ 0 = 1 by rfl, mul_one]
          congr
          rw [Finset.mul_sum] -- multiply x into the summation
          have : ∑ i ∈ Finset.Ico 0 (n + 1), x * (a (i + 1) * x ^ i) = ∑ i ∈ Finset.Ico 0 (n + 1), (a (i + 1) * x ^ (i + 1)) := by
            congr; ext; ring  -- and reform the formula inside the summation
          rw [this]

          -- we are done by adjusting the summation range
          rw [Finset.sum_Ico_add' (fun i ↦ a (i) * x ^ i) 0 (n + 1) 1]
          linarith

      -- we also need a simple fact that ∑ i ∈ Finset.range (k + 1), a' i = ∑ i ∈ Finset.Ico 1 (k + 2), a i
      have sum_a' : ∑ i ∈ Finset.range (k + 1), a' i = ∑ i ∈ Finset.Ico 1 (k + 2), a i := by
        unfold a'
        rw [Finset.range_eq_Ico]
        rw [show 1 = 0 + 1 by ring, show k + 2 = k + 1 + 1 by ring]
        rw [Finset.sum_Ico_add']

      -- LHS will be shown to be ≤ max (a 0) (∑ i ∈ Finset.range (k + 2), a i)
      -- we split into cases according to which is bigger
      by_cases h : a 0 ≤ ∑ i ∈ Finset.range (k + 2), a i
      · -- if ∑ i ∈ Finset.range (k + 2), a i is bigger, we use k + 1
        use k + 1
        constructor
        · -- clearly k + 1 ∈ [0, n + 1], as k ∈ [0, n]
          apply Finset.mem_Icc.mpr
          simp
          linarith

        -- given x ∈ [0, 1], we need to show the bound
        -- ∑ i ∈ Finset.range (n + 2), a i * x ^ i ≤ ∑ i ∈ Finset.range (k + 2), a i
        intro x xmem

        -- take x into induction hypothesis
        have ih_x := hk x xmem
        -- rewrite LHS using the sequence a'
        rw [h_sum_succ x]

        -- by the lemma at the beginning,
        -- LHS is bounded by max (a 0) (a 0 + ∑ i ∈ Finset.range (n + 1), a' i * x ^ i)
        trans max (a 0) (a 0 + ∑ i ∈ Finset.range (n + 1), a' i * x ^ i)
        nth_rw 1 [mul_comm]
        apply lem xmem

        -- by i.h.,  ∑ i ∈ Finset.range (n + 1), a' i * x ^ i ≤ ∑ i ∈ Finset.range (k + 1), a' i
        trans max (a 0) (a 0 + ∑ i ∈ Finset.range (k + 1), a' i)
        apply max_le_max_left
        exact (add_le_add_iff_left (a 0)).mpr ih_x

        -- and a 0 + ∑ i ∈ Finset.range (k + 1), a' i = ∑ i ∈ Finset.range (k + 2), a i, we are done
        rw [sum_a']
        rw [← Finset.sum_eq_sum_Ico_succ_bot]
        rw [← Finset.range_eq_Ico]
        rw [show k + 1 + 1 = k + 2 by ring]
        rw [max_eq_right h]
        linarith

      · -- if a 0 is bigger, we use k = 0
        use 0
        simp
        push_neg at h

        -- given x ∈ [0, 1], we need to show the bound ∑ i ∈ Finset.range (n + 1 + 1), a i * x ^ i ≤ a 0
        intro x x_ge x_le

        -- take x into induction hypothesis
        have ih_x := hk x ⟨x_ge, x_le⟩

        -- rewrite LHS using the sequence a'
        rw [h_sum_succ x]

        -- by the lemma at the beginning,
        -- LHS is bounded by max (a 0) (a 0 + ∑ i ∈ Finset.range (n + 1), a' i * x ^ i)
        trans max (a 0) (a 0 + ∑ i ∈ Finset.range (n + 1), a' i * x ^ i)
        nth_rw 1 [mul_comm]
        apply lem ⟨x_ge, x_le⟩

        -- by i.h.,  ∑ i ∈ Finset.range (n + 1), a' i * x ^ i ≤ ∑ i ∈ Finset.range (k + 1), a' i
        trans max (a 0) (a 0 + ∑ i ∈ Finset.range (k + 1), a' i)
        apply max_le_max_left
        exact (add_le_add_iff_left (a 0)).mpr ih_x

        -- replace a 0 + ∑ i ∈ Finset.range (k + 1), a' i = ∑ i ∈ Finset.range (k + 2), a i,
        -- we are done as in this case a 0 is bigger than ∑ i ∈ Finset.range (k + 2), a i
        rw [sum_a']
        rw [← Finset.sum_eq_sum_Ico_succ_bot]
        rw [← Finset.range_eq_Ico]
        rw [max_eq_left (le_of_lt h)]
        linarith
