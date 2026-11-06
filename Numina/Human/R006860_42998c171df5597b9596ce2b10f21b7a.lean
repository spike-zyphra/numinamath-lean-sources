import Mathlib
/- Let $M$ be a positive integer. Three pairwise distinct positive integers $a, b, c$, with $\operatorname{gcd}(a, b, c)=1$, satisfy
$$
Ma\left|(b-c)^{2}, \quad Mb\right|(c-a)^{2} \quad \text { and } \quad Mc \mid(a-b)^{2}.
$$
Prove that there does not exist a non-degenerate triangle with side lengths $a, b, c$. -/
theorem number_theory_641845 (m a b c : ℤ) (hm : m > 0) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (h1 : m * a ∣ (b - c) ^ 2) (h2 : m * b ∣ (c - a) ^ 2) (h3 : m * c ∣ (a - b) ^ 2) (h : Int.gcd a (Int.gcd b c) = 1) : a + b > c ∧ b + c > a ∧ c + a > b → False:= by
  -- Introduce the triangle inequality conditions
  intro ⟨g1, g2, g3⟩
  -- Remove the factor m from divisibility conditions
  replace h1 : a ∣ (b - c) ^ 2:= by exact dvd_of_mul_left_dvd h1
  replace h2 : b ∣ (c - a) ^ 2:= by exact dvd_of_mul_left_dvd h2
  replace h3 : c ∣ (a - b) ^ 2:= by exact dvd_of_mul_left_dvd h3
  clear m hm
  -- Prove that gcd(b,c) = 1
  have h4 : Int.gcd b c = 1:= by
    -- Set d = gcd(b,c) and work with it
    set d:= Int.gcd b c with hd
    clear_value d
    -- Show that d divides b
    have hb1 : (↑d : ℤ) ∣ b:= by
      subst d
      exact Int.gcd_dvd_left
    -- Show that d divides c
    have hc1 : (↑d : ℤ) ∣ c:= by
      subst d
      exact Int.gcd_dvd_right
    -- Express b and c in terms of d
    rcases hb1 with ⟨b1, hb1⟩
    rcases hc1 with ⟨c1, hc1⟩
    subst b c
    -- Show that d divides (a - d*b1)^2
    replace h3 : (↑d : ℤ) ∣ (a - ↑d * b1) ^ 2:= by exact dvd_of_mul_right_dvd h3
    -- Expand the square
    rw [show (a - ↑d * b1) ^ 2 = a ^ 2 + d * (d * b1 ^ 2 - 2 * b1 * a) by ring] at h3
    -- Show that d divides a^2
    replace h3 : (↑d : ℤ) ∣ a ^ 2:= by
      have h4 : (↑d : ℤ) ∣ d * (d * b1 ^ 2 - 2 * b1 * a):= by simp
      exact (Int.dvd_iff_dvd_of_dvd_add h3).mpr h4
    -- Use coprimality of a and d
    replace h : IsCoprime a (↑d : ℤ):= by exact Int.isCoprime_iff_gcd_eq_one.mpr h
    replace h : IsCoprime (a ^ 2) (↑d : ℤ):= by exact IsCoprime.pow_left h
    have h4 : (↑d : ℤ) ∣ (↑d : ℤ):= by simp
    -- Show that d divides gcd(a^2, d)
    replace h3 : (↑d : ℤ) ∣ Int.gcd (a ^ 2) (↑d : ℤ):= by exact Int.dvd_gcd h3 h4
    replace h : Int.gcd (a ^ 2) (↑d : ℤ) = 1:= by exact Int.isCoprime_iff_gcd_eq_one.mp h
    rw [h] at h3
    simp at h3
    -- Convert to natural numbers and conclude d = 1
    replace h3 : d ∣ 1:= by
      zify
      exact h3
    simp at h3
    exact h3
  clear h
  -- Prove that gcd(a,b) = 1
  have h5 : Int.gcd a b = 1:= by
    -- Set d = gcd(a,b) and work with it
    set d:= Int.gcd a b with hd
    clear_value d
    -- Show that d divides a
    have ha1 : (↑d : ℤ) ∣ a:= by
      subst d
      exact Int.gcd_dvd_left
    -- Show that d divides b
    have hb1 : (↑d : ℤ) ∣ b:= by
      subst d
      exact Int.gcd_dvd_right
    -- Express a and b in terms of d
    rcases ha1 with ⟨a1, ha1⟩
    rcases hb1 with ⟨b1, hb1⟩
    subst a b
    -- Show that d divides (c - d*a1)^2
    replace h2 : (↑d : ℤ) ∣ (c - ↑d * a1) ^ 2:= by exact dvd_of_mul_right_dvd h2
    -- Expand the square
    rw [show (c - ↑d * a1) ^ 2 = c ^ 2 + d * (d * a1 ^ 2 - 2 * a1 * c) by ring] at h2
    have h4 : (↑d : ℤ) ∣ d * (d * a1 ^ 2 - 2 * a1 * c):= by simp
    -- Show that d divides c^2
    replace h2 : (↑d : ℤ) ∣ c ^ 2:= by
      have h4 : (↑d : ℤ) ∣ d * (d * a1 ^ 2 - 2 * a1 * c):= by simp
      exact (Int.dvd_iff_dvd_of_dvd_add h2).mpr h4
    clear h4
    -- Use coprimality of d and c
    replace h4 : IsCoprime (↑d : ℤ) c:= by
      replace h4 : IsCoprime (↑d * b1) c:= by exact Int.isCoprime_iff_gcd_eq_one.mpr h4
      exact IsCoprime.symm (IsCoprime.of_mul_right_left (id (IsCoprime.symm h4)))
    replace h4 : IsCoprime (↑d : ℤ) (c ^ 2):= by exact IsCoprime.pow_right h4
    replace h4 : Int.gcd (↑d : ℤ) (c ^ 2) = 1:= by exact Int.isCoprime_iff_gcd_eq_one.mp h4
    have h5 : (↑d : ℤ) ∣ (↑d : ℤ):= by simp
    -- Show that d divides gcd(d, c^2)
    replace h2 : (↑d : ℤ) ∣ Int.gcd (↑d : ℤ) (c ^ 2):= by exact Int.dvd_gcd h5 h2
    rw [h4] at h2
    simp at h2
    -- Convert to natural numbers and conclude d = 1
    replace h2 : d ∣ 1:= by
      zify
      exact h2
    simp at h2
    exact h2
  -- Prove that gcd(c,a) = 1
  have h6 : Int.gcd c a = 1:= by
    -- Set d = gcd(c,a) and work with it
    set d:= Int.gcd c a with hd
    clear_value d
    -- Show that d divides c
    have hc1 : (↑d : ℤ) ∣ c:= by
      subst d
      exact Int.gcd_dvd_left
    -- Show that d divides a
    have ha1 : (↑d : ℤ) ∣ a:= by
      subst d
      exact Int.gcd_dvd_right
    -- Express c and a in terms of d
    rcases hc1 with ⟨c1, hc1⟩
    rcases ha1 with ⟨a1, ha1⟩
    subst a c
    -- Show that d divides (d*a1 - b)^2
    replace h3 : (↑d : ℤ) ∣ (↑d * a1 - b) ^ 2:= by exact dvd_of_mul_right_dvd h3
    -- Expand the square
    rw [show (↑d * a1 - b) ^ 2 = b ^ 2 + d * (d * a1 ^ 2 - 2 * a1 * b) by ring] at h3
    -- Show that d divides b^2
    replace h3 : (↑d : ℤ) ∣ b ^ 2:= by
      have h4 : (↑d : ℤ) ∣ d * (d * a1 ^ 2 - 2 * a1 * b):= by simp
      exact (Int.dvd_iff_dvd_of_dvd_add h3).mpr h4
    clear h4
    -- Use coprimality of d and b
    replace h5 : IsCoprime ((↑d : ℤ) * a1) b:= by exact Int.isCoprime_iff_gcd_eq_one.mpr h5
    replace h5 : IsCoprime (↑d : ℤ) b:= by exact IsCoprime.symm (IsCoprime.of_mul_right_left (id (IsCoprime.symm h5)))
    replace h5 : IsCoprime (↑d : ℤ) (b ^ 2):= by exact IsCoprime.pow_right h5
    replace h5 : Int.gcd (↑d : ℤ) (b ^ 2) = 1:= by exact Int.isCoprime_iff_gcd_eq_one.mp h5
    have h6 : (↑d : ℤ) ∣ (↑d : ℤ):= by simp
    -- Show that d divides gcd(d, b^2)
    replace h3 : (↑d : ℤ) ∣ Int.gcd (↑d : ℤ) (b ^ 2):= by exact Int.dvd_gcd h6 h3
    rw [h5] at h3
    simp at h3
    -- Convert to natural numbers and conclude d = 1
    replace h3 : d ∣ 1:= by
      zify
      exact h3
    simp at h3
    exact h3
  -- Show that one of a, b, c must be the largest
  have h7 : a > b ∧ a > c ∨ b > c ∧ b > a ∨ c > a ∧ c > b:= by omega
  -- Key lemma: if a is the largest side and triangle inequality holds, then contradiction
  have h8 : ∀ a b c : ℤ, a > 0 → b > 0 → c > 0 → a > b ∧ a > c → Int.gcd b c = 1 → b + c - a > 0 → b ∣ (c - a) ^ 2 → c ∣ (a - b) ^ 2 → False:= by
    intro a b c _ hb hc h1 h2 h3 h4 h5
    -- Expand (c-a)^2 in terms of (b+c-a)
    rw [show (c - a) ^ 2 = (b + c - a) ^ 2 + b * (2 * a - 2 * c - b) by ring_nf] at h4
    -- Show that b divides (b+c-a)^2
    replace h4 : b ∣ (b + c - a) ^ 2:= by
      have g1 : b ∣ b * (2 * a - 2 * c - b):= by simp
      exact (Int.dvd_iff_dvd_of_dvd_add h4).mpr g1
    -- Expand (a-b)^2 in terms of (b+c-a)
    rw [show (a - b) ^ 2 = (b + c - a) ^ 2 + c * (2 * a - 2 * b - c) by ring_nf] at h5
    -- Show that c divides (b+c-a)^2
    replace h5 : c ∣ (b + c - a) ^ 2:= by
      have g1 : c ∣ c * (2 * a - 2 * b - c):= by simp
      exact (Int.dvd_iff_dvd_of_dvd_add h5).mpr g1
    -- Use coprimality of b and c
    replace h2 : IsCoprime b c:= by exact Int.isCoprime_iff_gcd_eq_one.mpr h2
    -- Show that b*c divides (b+c-a)^2
    replace h4 : b * c ∣ (b + c - a) ^ 2:= by exact IsCoprime.mul_dvd h2 h4 h5
    -- Convert to natural numbers
    replace h4 : (b * c).natAbs ∣ ((b + c - a) ^ 2).natAbs:= by exact Int.natAbs_dvd_natAbs.mpr h4
    have g1 : ((b + c - a) ^ 2).natAbs > 0:= by positivity
    replace h4:= Nat.le_of_dvd g1 h4
    zify at h4
    rw [abs_of_pos (by positivity)] at h4
    rw [abs_of_pos (by positivity)] at h4
    -- Extract the inequalities from h1
    rcases h1 with ⟨h1, h⟩
    -- Show that b > b+c-a and c > b+c-a
    replace h : b > b + c - a:= by omega
    replace h1 : c > b + c - a:= by omega
    -- Show that b*c > (b+c-a)^2, which contradicts the divisibility
    replace h : b * c > (b + c - a) * (b + c - a):= by exact mul_lt_mul_of_pos' h h1 h3 hb
    linarith
  -- Apply the lemma to each case where one side is largest
  rcases h7 with h7 | h7 | h7
  .
    -- Case: a is the largest
    exact h8 a b c ha hb hc h7 h4 (by omega) h2 h3
  .
    -- Case: b is the largest
    exact h8 b c a hb hc ha h7 h6 (by omega) h3 h1
  .
    -- Case: c is the largest
    exact h8 c a b hc ha hb h7 h5 (by omega) h1 h2
