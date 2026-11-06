import Mathlib

/- For three positive integers $a,b$ and $c,$ if $\text{gcd}(a,b,c)=1$ and $a^2+b^2+c^2=2(ab+bc+ca),$ prove that all of $a,b,c$ is perfect square.  -/
theorem number_theory_34793 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : Int.gcd (Int.gcd a b) c = 1) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a * b + b * c + c * a)) : IsSquare a ∧ IsSquare b ∧ IsSquare c:= by
  -- Rewrite the main equation into three useful identities
  have h3 : (a + b - c) ^ 2 = 2 ^ 2 * (a * b):= by linarith
  have h4 : (a + c - b) ^ 2 = 2 ^ 2 * (a * c):= by linarith
  have h5 : (b + c - a) ^ 2 = 2 ^ 2 * (b * c):= by linarith

  -- Show that 2 divides each of the squared expressions
  have g1 : 2 ∣ (a + b - c) ^ 2:= by rw [h3] ; omega
  have g2 : 2 ∣ (a + c - b) ^ 2:= by rw [h4] ; omega
  have g3 : 2 ∣ (b + c - a) ^ 2:= by rw [h5] ; omega

  -- Use the fact that 2 is prime
  have g : Prime (2 : ℤ):= by exact Int.prime_two

  -- If a prime divides a square, it divides the base
  have g4 : 2 ∣ a + b - c:= by exact Prime.dvd_of_dvd_pow g g1
  have g5 : 2 ∣ a + c - b:= by exact Prime.dvd_of_dvd_pow g g2
  have g6 : 2 ∣ b + c - a:= by exact Prime.dvd_of_dvd_pow g g3

  -- Express each divisibility relation with integer quotients
  rcases g4 with ⟨x, hx⟩
  rcases g5 with ⟨y, hy⟩
  rcases g6 with ⟨z, hz⟩

  -- Substitute these expressions into our earlier identities
  rw [hx] at h3
  rw [hy] at h4
  rw [hz] at h5

  -- Clean up unnecessary hypotheses
  clear g1 g2 g3 hx hy hz

  -- Simplify to show that the products are perfect squares
  replace h3 : a * b = x ^ 2:= by linarith
  replace h4 : a * c = y ^ 2:= by linarith
  replace h5 : b * c = z ^ 2:= by linarith

  -- Prove that gcd(a,b) = 1 using contradiction
  have g1 : Int.gcd a b = 1:= by
    set d:= Int.gcd a b with hd
    clear_value d
    by_contra H
    have hdpos : d > 0:= by subst d ; refine Int.gcd_pos_of_ne_zero_left b (by omega)
    replace H : d > 1:= by omega
    replace h1 : Int.gcd d (c ^ 2) = 1:= by refine Int.gcd_eq_one_iff_coprime.mpr (by refine IsCoprime.pow_right (by exact Int.isCoprime_iff_gcd_eq_one.mpr h1))
    have ga : (↑d : ℤ) ∣ a:= by subst d ; exact Int.gcd_dvd_left
    have gb : (↑d : ℤ) ∣ b:= by subst d ; exact Int.gcd_dvd_right
    rcases ga with ⟨a1, ha1⟩
    rcases gb with ⟨b1, hb1⟩
    subst a b
    rw [show 2 * (↑d * a1 * (↑d * b1) + ↑d * b1 * c + c * (↑d * a1)) = d * (2 * (d * a1 * b1 + b1 * c + c * a1)) by ring] at h2
    rw [show (↑d * a1) ^ 2 + (↑d * b1) ^ 2 + c ^ 2 = d * (d * a1 ^ 2 + d * b1 ^ 2) + c ^ 2 by ring] at h2
    replace h2 : (↑d : ℤ) ∣ (↑d : ℤ) * (d * a1 ^ 2 + d * b1 ^ 2) + c ^ 2:= by rw [h2] ; simp
    have h6 : (↑d : ℤ) ∣ (↑d : ℤ) * (d * a1 ^ 2 + d * b1 ^ 2):= by simp
    replace h2 : (↑d : ℤ) ∣ c ^ 2:= by exact (Int.dvd_iff_dvd_of_dvd_add h2).mp h6
    have h7 : (↑d : ℤ) ∣ (↑d : ℤ):= by simp
    replace h7 : (↑d : ℤ) ∣ 1:= by
      zify at h1
      rw [←h1]
      exact Int.dvd_gcd h7 h2
    replace h7 : d ∣ 1:= by
      zify
      exact h7
    simp at h7
    linarith

  -- Apply the theorem: if gcd(a,b)=1 and a*b is a square, then a and b are squares
  have g2:= Int.sq_of_gcd_eq_one g1 h3
  rcases g2 with ⟨e, he⟩
  rcases he with he | he
  .
    -- Case where a = e²
    subst a

    -- Show that e² divides x² and y²
    have g3 : e ^ 2 ∣ x ^ 2:= by rw [←h3] ; simp
    have g4 : e ^ 2 ∣ y ^ 2:= by rw [←h4] ; simp

    -- If e² divides x², then e divides x (using properties of absolute values)
    replace g3 : e ∣ x:= by
      apply Int.natAbs_dvd_natAbs.mp
      suffices e.natAbs ^ 2 ∣ x.natAbs ^ 2 by exact (Nat.pow_dvd_pow_iff (by omega)).mp this
      zify
      rw [show |e| ^ 2 = e ^ 2 by exact sq_abs e]
      rw [show |x| ^ 2 = x ^ 2 by exact sq_abs x]
      exact g3

    -- Similarly, if e² divides y², then e divides y
    replace g4 : e ∣ y:= by
      apply Int.natAbs_dvd_natAbs.mp
      suffices e.natAbs ^ 2 ∣ y.natAbs ^ 2 by exact (Nat.pow_dvd_pow_iff (by omega)).mp this
      zify
      rw [show |e| ^ 2 = e ^ 2 by exact sq_abs e]
      rw [show |y| ^ 2 = y ^ 2 by exact sq_abs y]
      exact g4

    -- Express x and y in terms of e
    rcases g3 with ⟨x1, hx1⟩
    rcases g4 with ⟨y1, hy1⟩
    subst x y

    -- Derive that b and c must be squares
    replace h3 : e ^ 2 * (b - x1 ^ 2) = 0:= by linarith
    replace h4 : e ^ 2 * (c - y1 ^ 2) = 0:= by linarith
    replace ha : e ^ 2 ≠ 0:= by linarith
    simp [ha] at h3 h4
    replace h3 : b = x1 ^ 2:= by linarith
    replace h4 : c = y1 ^ 2:= by linarith
    subst b c

    -- Conclude that a, b, and c are all perfect squares
    simp [IsSquare]
    refine ⟨by use e ; ring_nf, by use x1 ; ring_nf, by use y1 ; ring_nf⟩
  .
    -- Case where b = e² (which is impossible due to positivity constraints)
    have g2 : e ^ 2 ≥ 0:= by positivity
    linarith
