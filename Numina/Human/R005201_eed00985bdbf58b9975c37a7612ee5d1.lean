import Mathlib

/- Find the smallest possible value of the expression

$$
\left\lfloor\frac{a+b+c}{d}\right\rfloor+\left\lfloor\frac{b+c+d}{a}\right\rfloor+\left\lfloor\frac{c+d+a}{b}\right\rfloor+\left\lfloor\frac{d+a+b}{c}\right\rfloor,
$$

in which $a, b, c$ and $d$ vary over the set of positive integers.

(Here $\lfloor x\rfloor$ denotes the biggest integer which is smaller than or equal to $x$.)

-/
theorem number_theory_606243 :
    IsLeast {x : ℤ | ∃ a b c d : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ x = ⌊(a + b + c : ℝ) / d⌋ + ⌊(b + c + d : ℝ) / a⌋ + ⌊(c + d + a : ℝ) / b⌋ + ⌊(d + a + b : ℝ) / c⌋} 9 := by
  -- It has no harm to assume a, b, c, d are integer type, not natural number type.
  -- Break the goals into two parts.
  simp only [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First, prove 9 is attainable.
    use 5, 5, 5, 4
    norm_num
  . -- Then, prove that 9 is indeed a lower bound.
    -- Extracting useful information from the hypothesis.
    rw [Set.mem_setOf]
    intro x
    rw [Set.mem_setOf]
    rintro ⟨a, b, c, d, ha, hb, hc, hd, hx⟩
    -- The condition 9 ≤ ... is equivalent to 8 < ... since we are considering only the integers.
    suffices 8 < x by
      omega
    rw [hx]
    clear hx
    -- Prove a lemma that x / y + y / x ≥ 2 for x, y > 0.
    have lemma₀ (x y : ℤ) (hx : 0 < x) (hy : 0 < y) : 2 ≤ (x : ℝ) / y + (y : ℝ) / x := by
      -- Basically this is equivalent to (√(x / y) - √(y / x))² ≥ 0.
      have := sq_nonneg (Real.sqrt ((x : ℝ) / y) - Real.sqrt ((y : ℝ) / x))
      rw [sub_sq, Real.sq_sqrt, Real.sq_sqrt, mul_assoc, <-Real.sqrt_mul] at this
      field_simp at this ⊢
      rw [le_div_iff₀] at this ⊢
      linarith only [this]
      all_goals
        positivity
    -- Now remains to prove that 8 < ⌊(a + b + c : ℝ) / d⌋ + ⌊(b + c + d : ℝ) / a⌋ + ⌊(c + d + a : ℝ) / b⌋ + ⌊(d + a + b : ℝ) / c⌋.
    -- The key idea is to use the fact that ⌊x⌋ > x - 1.
    rify
    calc
      8 ≤ ((a : ℝ) / b + (b : ℝ) / a) + ((a : ℝ) / c + (c : ℝ) / a) + ((a : ℝ) / d + (d : ℝ) / a) + ((b : ℝ) / c + (c : ℝ) / b) + ((b : ℝ) / d + (d : ℝ) / b) + ((c : ℝ) / d + (d : ℝ) / c) - 4 := by
        -- Use lemma₀ to prove the inequality.
        have h₁ := lemma₀ a b ha hb
        have h₂ := lemma₀ a c ha hc
        have h₃ := lemma₀ a d ha hd
        have h₄ := lemma₀ b c hb hc
        have h₅ := lemma₀ b d hb hd
        have h₆ := lemma₀ c d hc hd
        linarith only [h₁, h₂, h₃, h₄, h₅, h₆]
      _ = ((a + b + c : ℝ) / d - 1) + ((b + c + d : ℝ) / a - 1) + ((c + d + a : ℝ) / b - 1) + ((d + a + b : ℝ) / c - 1) := by
        -- Rewrite the R.H.S. to $\left(\frac{a}{b}+\frac{b}{a}\right)+\left(\frac{a}{c}+\frac{c}{a}\right)+\left(\frac{a}{d}+\frac{d}{a}\right)+\left(\frac{b}{c}+\frac{c}{b}\right)+\left(\frac{b}{d}+\frac{d}{b}\right)+\left(\frac{c}{d}+\frac{d}{c}\right)$.
        field_simp
        ring
      _ < ⌊(a + b + c : ℝ) / d⌋ + ⌊(b + c + d : ℝ) / a⌋ + ⌊(c + d + a : ℝ) / b⌋ + ⌊(d + a + b : ℝ) / c⌋ := by
        -- Use the fact that ⌊x⌋ > x - 1.
        have h₁ := Int.sub_one_lt_floor ((a + b + c : ℝ) / d)
        have h₂ := Int.sub_one_lt_floor ((b + c + d : ℝ) / a)
        have h₃ := Int.sub_one_lt_floor ((c + d + a : ℝ) / b)
        have h₄ := Int.sub_one_lt_floor ((d + a + b : ℝ) / c)
        linarith only [h₁, h₂, h₃, h₄]
