import Mathlib

/- 3. Substituting the natural number $n$ into $n^{3}-n$, the following result can be obtained ( ).
A. 678927
B. 695644
C. 728910
D. 874231
E. 934508 -/
theorem number_theory_112399 {A B C D E : ℕ} {valid_prop : ℕ → Prop}
    (h_choices : A = 678927 ∧ B = 695644 ∧ C = 728910 ∧ D = 874321 ∧ E = 934508)
    (h_valid_prop : ∀ x, valid_prop x = ∃ n : ℕ, x = n ^ 3 - n) :
    {x | (x ∈ ({A, B, C, D, E} : Finset ℕ)) ∧ valid_prop x} = {C} := by

  -- we start by noting that \( n^3 - n \) can be factored as \( n(n - 1)(n + 1) \), which is the product of three consecutive integers.
  have h1 (n : ℕ) : n ^ 3 - n = (n - 1) * n * (n + 1) := by
    rcases n.eq_zero_or_pos with hn | hn
    -- if $n = 0$
    . norm_num [hn]
    -- if $n \ne 0$
    zify
    rw [Nat.cast_sub (Nat.le_self_pow three_ne_zero n)]
    rw [Nat.cast_sub (by linarith)]
    rw [Nat.cast_pow, Nat.cast_one]
    ring

  -- This product is always divisible by 6.
  have h2 (n : ℕ) : 6 ∣ n ^ 3 - n := by
    rcases n.eq_zero_or_pos with hn | hn
    -- if $n = 0$
    . norm_num [hn]
    -- if $n \ne 0$
    have (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      trans n % 6 * (n % 6 + 1) * (n % 6 + 2) % 6
      . simp [Nat.mul_mod]
      have : n % 6 < 6 := Nat.mod_lt n (by linarith only)
      interval_cases n % 6 <;> norm_num
    convert this (n - 1) using 1
    rw [h1, show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega]

  -- If a number isn't divisible by 6, it can be eliminated.
  have h3 (n : ℕ) : ¬ 6 ∣ n → ¬ valid_prop n := by
    by_contra!
    rw [h_valid_prop] at this
    obtain ⟨h_ndvd, ⟨k, hk⟩⟩ := this
    simp_all

  -- A is not valid as it is not divided by 6
  have h_checkA : ¬ valid_prop A := by
    apply h3
    norm_num [h_choices]

  -- B is not valid as it is not divided by 6
  have h_checkB : ¬ valid_prop B := by
    apply h3
    norm_num [h_choices]

  -- C is divided by 6
  have h_checkC : 6 ∣ C := by
    norm_num [h_choices]

  -- D is not valid as it is not divided by 6
  have h_checkD : ¬ valid_prop D := by
    apply h3
    norm_num [h_choices]

  -- E is not valid as it is not divided by 6
  have h_checkE : ¬ valid_prop E := by
    apply h3
    norm_num [h_choices]

  -- Next, we verify if 728910 can be expressed as $ n^3 - n $. 728910 is indeed $ 90^3 - 90 $.
  have h_valid_C : valid_prop C := by
    simp only [h_choices, h_valid_prop]
    use 90
    norm_num

  -- Therefore, the correct answer is $\boxed{C}$.
  ext x
  constructor
  . simp
    intro hx h_x_valid
    rcases hx with hx | hx | hx | hx | hx
    all_goals rw [hx] at h_x_valid
    any_goals contradiction
    -- one goal left, the condition x = C
    exact hx
  . simp_all
