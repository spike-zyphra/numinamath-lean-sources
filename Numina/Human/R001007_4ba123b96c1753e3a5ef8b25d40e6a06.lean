import Mathlib
/-A number is selected at random from 1 through 100, inclusive.  What is the probability that the number is a divisor of 50? Express your answer as a common fraction.-/
set_option maxRecDepth 5000000
theorem algebra_19774 {n : ℕ} (q : ℚ)(hn : n ∈ Finset.Icc 1 100)
  (hq : q =Rat.divInt z1 z2 ) (hz: z1=  Set.ncard {n | n ∈ Finset.Icc 1 100 ∧ 50 % n = 0}) (hz2 : z2= (Finset.Icc (1: ℕ ) 100 ).card): q.num / q.den = 3 / 50:= by
  norm_num at hz2
  --There are 100 numbers possible between 1 and 100. There are 6 divisors of 50: 1,2,5,10,25,50.
  have heq : {n | n ∈ Finset.Icc 1 100 ∧ 50 % n = 0} = {1,2,5,10,25,50} := by
    simp
    ext n
    constructor
    .
      simp
      intro hn1 hn2 hn3
      have hn4 : n < 101 := by
        linarith
      rw [← Finset.mem_range] at hn4
      fin_cases hn4
      any_goals contradiction
      all_goals simp
    .
      simp
      intro hn1
      cases hn1 with
      | inl h =>rw[h]; simp
      | inr h =>cases h with
        | inl h => rw[h]; simp
        | inr h => cases h with
          | inl h => rw[h]; simp
          | inr h => cases h with
            | inl h => rw[h]; simp
            | inr h => cases h with
              | inl h => rw[h]; simp
              | inr h => rw[h]; simp
  rw [heq] at hz; norm_num at hz
  -- So the probability that a randomly selected number is a divisor of 50 is $\dfrac{6}{100} = \boxed{\dfrac{3}{50}}$.
  rw [hz] at hq ; rw [hz2] at hq; rw [hq]
  rw [Rat.num_mk]; rw [Rat.den_mk]
  ring_nf; rw[Int.sign.eq_def]
  norm_num
