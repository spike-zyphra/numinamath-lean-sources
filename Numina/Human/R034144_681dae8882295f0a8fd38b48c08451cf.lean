import Mathlib

/- Define a sequence recursively by f_1(x)=∣x−1∣ and f_n(x)=f_{n−1}(∣x−n∣) for integers n>1.
Find the least value of n such that the sum of the zeros of f_n​ exceeds 500,000. -/
theorem algebra_98359 {f : ℕ → ℝ → ℝ}
    (hf1 : ∀ x, f 1 x = |x - 1|)
    (hfn : ∀ n > 1, ∀ x, f n x = f (n - 1) |x - n|) :
    IsLeast {n | n > 0 ∧ ∑ᶠ z ∈ {z | f n z = 0}, z > 500000} 101 := by
  -- prove some auxiliary results about converting n * (n + 1) / 2 from ℕ (ℤ) to ℝ
  have div2 n : 2 ∣ n * (n + 1) := by
    apply Even.two_dvd
    exact Nat.even_mul_succ_self n
  have div2_cast (n : ℕ) : (((n * (n + 1) / 2) : ℕ) : ℝ) = (n : ℝ) * (n + 1) / 2 := by
    rw [Nat.cast_div (div2 n) (by norm_num)]
    norm_cast
  have div2_cast_z (n : ℤ) : (((n * (n + 1) / 2) : ℤ) : ℝ) = (n : ℝ) * (n + 1) / 2 := by
    rw [Int.cast_div _ (by norm_num)]
    norm_cast
    apply Even.two_dvd
    exact Int.even_mul_succ_self n
  -- let a(n) = n - n * (n - 1) / 2
  set a : ℕ → ℝ := fun n => n - n * (n - 1) / 2
  -- show that any zero z of f(n + 1) can be written as
  -- z = a(n + 1) + 2 * i for 0 ≤ 2 * i ≤ n * (n + 1)
  have hzeros n : {z | f (n + 1) z = 0} =
      (fun (i : ℕ) => a (n + 1) + 2 * (i : ℝ)) '' Finset.range (n * (n + 1) / 2 + 1) := by
    have a_sub_n n : a (n + 1 + 1) - (n + 1 + 1) = -(n + 1) * (n + 2) / 2 := by simp [a]; ring
    -- proof by induction
    induction n with
    -- the base case is easy: f 1 z = |z - 1| so z = 1
    | zero => simp [hf1, a]; ext z; simp [sub_eq_zero]
    | succ n ih =>
      ext z; simp
      simp [hfn]
      rw [show f (n + 1) |z - (n + 1 + 1)| = 0 ↔ |z - (n + 1 + 1)| ∈ {z | f (n + 1) z = 0} by rfl]
      -- by induction hypothesis we have that f (n + 2) z = 0 iff f (n + 1) |z - (n + 2)| = 0
      simp [ih]
      constructor
      -- assume that f (n + 1) |z - (n + 2)| = 0, i.e., |z - (n + 2)| = a(n + 1) + 2 * i, 0 ≤ 2 * i ≤ n * (n + 1)
      · intro ⟨i, hi, heq⟩
        -- consider two cases z < n + 2 and n + 2 ≤ z
        cases' lt_or_le z (n + 1 + 1) with hz hz
        -- if z < n + 2 then |z - (n + 2)| = n + 2 - z
        · rw [abs_of_neg (by linarith)] at heq
          -- we have z = (n + 2) - 2 * i - a (n + 1)
          rw [show z = (n + 1 + 1) - 2 * i - a (n + 1) by linarith] at hz ⊢
          -- we will show that z can be written as
          -- z = a (n + 2) + 2 * j with 0 ≤ 2 * j ≤ (n + 1) * (n + 2)
          -- take j = n * (n + 1) / 2 - i and prove everything with simple algebraic manipulations
          use n * (n + 1) / 2 - i
          have hineq : i ≤ n * (n + 1) / 2 := by omega
          simp [a] at hz ⊢
          push_cast [hineq, div2_cast]
          constructor
          · rify [hineq, div2_cast_z]
            linarith
          · ring
        -- if n + 2 ≤ z then |z - (n + 2)| = z - (n + 2)
        · rw [abs_of_nonneg (by linarith)] at heq
          -- we have z = a (n + 1) + 2 * i - (n + 2)
          rw [show z = a (n + 1) + 2 * i + (n + 1 + 1) by linarith] at hz ⊢
          simp [a] at hz ⊢
          -- we will show that z can be written as
          -- z = a (n + 2) + 2 * j with 0 ≤ 2 * j ≤ (n + 1) * (n + 2)
          -- take j = i + n + 1 and prove everything with simple algebraic manipulations
          use i + n + 1
          constructor
          · rify [div2_cast_z] at hi ⊢
            linarith
          · push_cast
            ring
      -- assume now that f (n + 2) z = 0, i.e., z = a(n + 2) + 2 * i, 0 ≤ 2 * i ≤ (n + 1) * (n + 2)
      -- we have to show that |z - (n + 2)| = |-(n + 1) * (n + 2) / 2 + 2 * i| is a zero of f (n + 1)
      · intro ⟨i, hi, heq⟩
        rw [←heq, add_sub_right_comm, a_sub_n]
        -- consider two cases: 2 * i < (n + 1) * (n + 2) / 2 and 2 * i ≥ (n + 1) * (n + 2) / 2
        cases' lt_or_le (2 * (i : ℝ)) ((n + 1) * (n + 2) / 2) with hi2 hi2
        · rw [abs_of_neg (by linarith)]
          -- if 2 * i < (n + 1) * (n + 2) / 2 then we need to show that
          -- (n + 1) * (n + 2) / 2 - 2 * i = a (n + 1) + 2 * j for some j, 0 ≤ 2 * j ≤ n * (n + 1)
          -- take j = n * (n + 1) / 2 - i
          use n * (n + 1) / 2 - i
          -- show that i ≤ n * (n + 1) / 2 (we need this inequality to convert results from ℕ to ℝ)
          have hineq : i ≤ n * (n + 1) / 2 := by
            -- consider 3 cases: n = 0, n = 1, or n ≥ 2
            rcases show n = 0 ∨ n = 1 ∨ n ≥ 2 by omega with hn | hn | hn
            · rw [hn] at hi2 ⊢
              norm_num at hi2
              norm_cast at hi2
              omega
            · rw [hn] at hi2 ⊢
              norm_num at hi2
              norm_cast at hi2
              omega
            · rify at hn ⊢
              push_cast [div2_cast_z]
              nlinarith
          -- all results follow from simple algebraic manipulations
          constructor
          · omega
          · simp only [a]
            push_cast [hineq, div2_cast]
            ring
        · rw [abs_of_nonneg (by linarith)]
          -- if 2 * i ≥ (n + 1) * (n + 2) / 2 then we need to show that
          -- 2 * i - (n + 1) * (n + 2) / 2 = a (n + 1) + 2 * j for some j, 0 ≤ 2 * j ≤ n * (n + 1)
          -- take j = i - (n + 1)
          use i - (n + 1)
          -- show that n + 1 ≤ i (we need this inequality to convert results from ℕ to ℝ)
          have hineq : n + 1 ≤ i := by
            -- consider 3 cases: n = 0, n = 1, or n ≥ 2
            rcases show n = 0 ∨ n = 1 ∨ n ≥ 2 by omega with hn | hn | hn
            · rw [hn] at hi2 ⊢
              norm_num at hi2
              norm_cast at hi2
              omega
            · rw [hn] at hi2 ⊢
              norm_num at hi2
              norm_cast at hi2
              omega
            · rify at hn ⊢
              nlinarith
          -- all results follow from simple algebraic manipulations
          constructor
          · rify [hineq, div2_cast_z]
            rify [div2_cast_z] at hi
            linarith
          · simp only [a]
            push_cast [hineq]
            ring
  -- compute the sum from the theorem statement using hzeros
  -- we get ∑ᶠ (zeros of f (n + 1))
  --            = ∑ i ∈ Finset.range (n * (n + 1) / 2 + 1), a (n + 1) + 2 * i
  --            = ((n + 1) ^ 3 + (n + 1) ^ 2 + 2 * (n + 1)) / 2
  have hsum n : ∑ᶠ z ∈ {z | f (n + 1) z = 0}, z = (((n : ℝ) + 1) ^ 3 - (n + 1) ^ 2 + 2 * (n + 1)) / 2 := by
    rw [hzeros]
    rw [finsum_mem_image (by intro i; simp), finsum_mem_coe_finset, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    simp [Finset.sum_const, a]
    have hsum_id := Finset.sum_range_id_mul_two (n * (n + 1) / 2 + 1)
    rify at hsum_id
    rw [mul_comm] at hsum_id
    rw [hsum_id]
    norm_num [div2_cast, div2_cast_z]
    ring
  -- prove that the lowest n for which the sum of zeros exceeds 500,000 is 101
  rw [IsLeast, lowerBounds, Set.mem_setOf_eq, hsum]
  -- it is easy to show that the sum of zeros is greater than 500,000 when n = 101
  norm_num
  intro n hn
  rw [show n = (n - 1) + 1 by omega, hsum]
  push_cast [hn]
  norm_num
  -- let g(n) = (n ^ 3 - n ^ 2 + 2 * n) / 2
  -- it is enough to show that g(n) is monotone and g(100) ≤ 500,000
  set g := fun n : ℕ => ((n : ℝ) ^ 3 - n ^ 2 + 2 * n) / 2
  suffices h : Monotone g ∧ g 100 ≤ 500000 by
    rw [show ((n : ℝ) ^ 3 - n ^ 2 + 2 * n) / 2 = g n by simp]
    intro hg
    contrapose! hg
    apply le_trans _ h.2
    apply h.1
    omega
  -- it is easy to show that g 100 ≤ 500,000
  norm_num
  -- prove that g n ≤ g (n + 1) for all n ∈ ℕ
  apply monotone_nat_of_le_succ
  intro i
  simp [← sub_nonneg, g]
  ring_nf
  positivity