import Mathlib


/-
Evaluate the sum

$$
1-2+3-4+\cdots+2007-2008
$$
-/
theorem algebra_608419 :  ∑ i ∈ Finset.range 2008, (-1 : ℤ)^i * (i + 1) = -1004 := by

  -- Some auxilary function to simplify the calculation
  let g : ℕ → ℤ := fun j => (-1 : ℤ)^j * (j + 1)
  let f : ℕ → ℤ := fun n => ∑ i ∈ Finset.range (n+1), g i

  -- We can sum f as sub of neighbour two terms, which is -1
  have hf (n:ℕ) : (f (2*n + 1) = -n - 1) := by
    -- This can be proved by induction on n
    induction' n with n hn

    -- 0 case
    simp;
    unfold f
    apply Finset.sum_range_succ

    -- Succ case
    calc
      _ = f (2 * n + 1 + 2) := by ring_nf
      _ = ∑ i ∈ Finset.range (2 * n + 1 + 2 + 1), g i := by
        unfold f; linarith

      -- Extract the last term in the sum
      _ = ∑ i ∈ Finset.range (2 * n + 1 + 2), g i + g (2 * n + 1 + 2) := by
        apply Finset.sum_range_succ
      _ = ∑ i ∈ Finset.range (2 * n + 1 + 1 + 1), g i + g (2 * n + 3) := by
        linarith
      -- Extract the last 2 term in the sum
      _ = ∑ i ∈ Finset.range (2 * n + 1 + 1), g i + g (2 * n + 1 + 1) + g (2 * n + 3) := by
        have : ∑ i ∈ Finset.range (2 * n + 1 + 1 + 1), g i = ∑ i ∈ Finset.range (2 * n + 1 + 1), g i + g (2 * n + 1 + 1) := by apply Finset.sum_range_succ
        rw [this]

      -- Calculate the result
      _ = f (2*n+1) + g (2 * n + 1 + 1) + g (2 * n + 3) := by
        unfold f; linarith
      _ = -↑n - 1 + g (2 * n + 1 + 1) + g (2 * n + 3) := by rw [hn]
      _ = -↑n - 1 + g (2 * n + 2) + g (2 * n + 3) := by ring_nf
      _ = -↑n - 1 + (-1 : ℤ)^(2 * n + 2) * (2 * n + 2 + 1) + (-1 : ℤ)^(2 * n + 3) * (2 * n + 3 + 1) := by unfold g; norm_num
      _ = - n - 1 + (2 * n + 2 + 1) - (2 * n + 3 + 1) := by

        -- 2 number facts of -1 power
        have _1 : (-1 : ℤ)^(2 * n + 2) = 1 := by
          calc
            _ = (-1 : ℤ)^(2 * n) * (-1 : ℤ)^2 := by apply pow_add
            _ = (-1 : ℤ)^(2 * n) := by norm_num
            _ = ((-1 : ℤ)^2)^ n := by apply pow_mul
            _ = 1^n := by norm_num
            _ = 1 := by ring_nf
        have _2 : (-1 : ℤ)^(2 * n + 3) = -1 := by
          calc
            _ = (-1 : ℤ)^(2 * n) * (-1 : ℤ)^3 := by apply pow_add
            _ = ((-1 : ℤ)^(2 * n)) * (-1) := by norm_num
            _ = -((-1 : ℤ)^(2 * n)) := by norm_num
            _ = -1 := by
              have : (-1 : ℤ)^(2 * n) = 1 := by
                calc
                  _ = ((-1 : ℤ)^2)^ n := by apply pow_mul
                  _ = 1^n := by norm_num
                  _ = 1 := by ring_nf
              rw [this]
        rw [_1, _2]
        ring_nf
      _ = _ := by ring_nf; field_simp; ring_nf

  -- The goal can be rewrite by f
  have : ∑ i ∈ Finset.range 2008, (-1 : ℤ)^i * (i + 1) = f 2007 := by
    unfold f g; ring_nf
  rw [this]
  -- rw f and use f (2n+1) = -n-1, since 2007 = 2*1003+1s
  have : f 2007 = -1004 := by
    calc
      _ = f (2*1003 + 1) := by norm_num
      _ = -1003 - 1 := by
        rw [hf]; norm_cast
      _ = -1004 := by norm_num
  exact this
