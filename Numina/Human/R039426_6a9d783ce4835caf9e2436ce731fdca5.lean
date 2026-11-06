import Mathlib

/- 9. Compute the sum of all real numbers $x$ such that

$$

2 x^{6}-3 x^{5}+3 x^{4}+x^{3}-3 x^{2}+3 x-1=0

$$
 -/
theorem algebra_191362 (f : ℝ → ℝ) (hf : f = fun x => 2*x^6 - 3*x^5 + 3*x^4 + x^3 - 3*x^2 + 3*x - 1) :
    ∑ᶠ x ∈ {x | f x = 0}, x = -1/2 := by
  -- first we'll prove the set of roots is {1/2, -1}
  have : {x | f x = 0} = ({1/2, -1} : Finset ℝ) := by
    ext x
    constructor <;> simp [hf] <;> rintro h
    -- to prove roots are subset of {1/2, -1}, write the expression as following factored form
    . replace h : (x^2 - x + 1) ^ 2 * (2 * x^2 + x - 1) = 0 := by linear_combination h
      -- the square is always positive by completing square
      have : 0 < (x ^ 2 - x + 1) ^ 2 := by
        apply sq_pos_of_pos
        convert_to 0 < (x - 1/2)^2 + 3 / 4
        . ring
        positivity
      -- so only 2x^2 + x - 1 needs to be solved, factor it out
      have : (x ^ 2 - x + 1) ^ 2 ≠ 0 := by linarith
      simp [this] at h
      -- we get x = 1/2 or x = -1
      replace h : (x - 1 / 2) * (x + 1) = 0 := by linear_combination h / 2
      simp at h
      rw [sub_eq_zero, ← eq_neg_iff_add_eq_zero] at h
      assumption
    -- other direction, plug in two values and see they are roots
    . obtain rfl | rfl := h <;> norm_num
  -- now convert the sum to a normal sum
  rw [this]
  rw_mod_cast [finsum_mem_finset_eq_sum]
  rw [Finset.sum_pair]
  . push_cast
    norm_num
  . push_cast
    norm_num