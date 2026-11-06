import Mathlib

/- the sum of properDivisors -/
abbrev sigma (n : ℕ) := ∑ d ∈ n.properDivisors, d

/- def amicable pair -/
abbrev is_amicable_pair (n m : ℕ) := (sigma n = m ∧ sigma m = n)

/-
Two positive integers $ m $ and $ n $ are called an amicable pair if the sum of the proper divisors of $ m $ (denoted as $ \sigma(m) $) equals $ n $, and the sum of the proper divisors of $ n $ equals $ m $. In other words, $ \sigma(m) = n $ and $ \sigma(n) = m $. Show that each of the following pairs of integers are amicable pairs:
a) 220, 284
b) 1184, 1210
c) 79750, 88730.
-/
theorem number_theory_4920 : (is_amicable_pair 220 284) ∧ (is_amicable_pair 1184 1210) ∧ (is_amicable_pair 79750 88730) := by

  have pa :is_amicable_pair 220 284 := by
    unfold is_amicable_pair sigma
    constructor <;> rfl

  have pb : is_amicable_pair 1184 1210 := by
    unfold is_amicable_pair sigma
    constructor <;> native_decide

  have pc : is_amicable_pair 79750 88730 := by
    unfold is_amicable_pair sigma
    constructor <;> native_decide

  exact ⟨pa, pb, pc⟩
