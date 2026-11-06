import Mathlib

/-
Does there exist any integer  $a,b,c$  such that  $a^2bc+2,ab^2c+2,abc^2+2$   are perfect squares?
-/

theorem number_theory_8574 (a b c : ℤ) :
    ¬ (IsSquare (a ^ 2 * b * c + 2) ∧
    IsSquare (a * b ^ 2 * c + 2) ∧
    IsSquare (a * b * c ^ 2 + 2)) := by

  intro ⟨h1, h2, h3⟩

  -- odd number mod 4 = 1 or 3
  have t_omod4 {x : ℤ} (h : Odd x) : x % 4 = 1 ∨ x % 4 = 3 := by
    obtain ⟨k, hk⟩ := h
    rw [hk]
    rcases k.even_or_odd with ⟨l, ho⟩ | ⟨l, ho⟩
    . rw [ho, ← two_mul, ← mul_assoc, show (2:ℤ) * 2 = 4 by norm_num, Int.add_emod]
      norm_num
    rw [ho, mul_add, ← mul_assoc, show (2:ℤ) * 2 = 4 by norm_num, add_assoc, Int.add_emod]
    norm_num


  -- perfect squqares mod 4 = 0 or 1
  have t_smod4 {x : ℤ} (h : IsSquare x) : x % 4 = 0 ∨ x % 4 = 1 := by
    obtain ⟨y, hy⟩ := h
    rcases y.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
    <;> rcases k.even_or_odd with ⟨l, hl⟩ | ⟨l, hl⟩
    all_goals rw [hk] at hy; ring_nf at hy; rw [hy]; norm_num


  -- None of a, b as well as c is even.If there is one,then there is a number congruent to 2(mod4) among the 3 given the numbers.Thus all of them cannot be squares.
  have t1 (a b c : ℤ)
      (h1 : IsSquare (a ^ 2 * b * c + 2)):
      Odd a := by
    by_contra ha; simp at ha
    have h_mod : (a ^ 2 * b * c + 2) % 4 = 2 := by
      have ⟨k, hk⟩ := ha
      rw [hk, ← two_mul, pow_two, ← mul_assoc, mul_assoc 2 k 2, mul_comm k 2, ← mul_assoc, show (2:ℤ) * 2 = 4 by norm_num,
          Int.add_emod, mul_assoc, mul_assoc, mul_assoc, Int.mul_emod_right 4]
      norm_num
    have := t_smod4 h1
    simp_all

  have ha_odd : Odd a := t1 a b c h1

  have hb_odd : Odd b := by
    apply t1 b c a
    rw [mul_comm, ← mul_assoc]
    exact h2

  have hc_odd : Odd c := by
    apply t1 c a b
    rw [mul_assoc, mul_comm]
    exact h3

  -- Now as they are all odd numbers there are only 2 congruent modulo 4 to be more specific 1,−1(mod4).. But there are 33 numbers.So by PHP two numbers have the same congruent (mod4).Let a and b be those 2 numbers(WLOG).Then by mere inspection, abc^2+2is congruent to 3(mod4) .
  have t2 (a b c : ℤ)
      (h1 : IsSquare (a ^ 2 * b * c + 2))
      (ha_odd : Odd a)
      (hb_odd : Odd b)
      (h : b % 4 = c % 4) :
      False := by
    -- a ^ 2 % 4 = 1
    have r1 : a ^ 2 % 4 = 1 := by
      have ⟨k, hk⟩ := ha_odd
      rw [hk, pow_two, show (2 * k + 1) * (2 * k + 1) = 4 * (k ^ 2 + k) + 1 by ring,
          Int.add_emod, Int.mul_emod]
      norm_num
    -- b * c % 4 = 1
    have r2 : b * c % 4 = 1 := by
      rw [Int.mul_emod, ← h, ← pow_two]
      have ⟨k, hk⟩ := hb_odd
      rw [hk, pow_two, ← Int.mul_emod,
          show (2 * k + 1) * (2 * k + 1) = 4 * (k ^ 2 + k) + 1 by ring,
          Int.add_emod, Int.mul_emod]
      norm_num
    -- (a ^ 2 * b * c + 2) % 4 = 3
    have r3 : (a ^ 2 * b * c + 2) % 4 = 3 := by
      rw [mul_assoc, Int.add_emod, Int.mul_emod, r1, r2]
      norm_num
    -- contradict
    have := t_smod4 h1
    simp_all

  -- at least two of them mod 4 are equal
  have : b % 4 = c % 4 ∨ c % 4 = a % 4 ∨ a % 4 = b % 4 := by
    rcases t_omod4 ha_odd with ha | ha
    <;> rcases t_omod4 hb_odd with hb | hb
    <;> rcases t_omod4 hc_odd with hc | hc
    all_goals omega

  rcases this with h | h | h

  -- done
  . exact t2 a b c h1 ha_odd hb_odd h
  . apply t2 b c a ?_ hb_odd hc_odd h
    rw [mul_comm, ← mul_assoc]
    exact h2
  . apply t2 c a b ?_ hc_odd ha_odd h
    rw [mul_assoc, mul_comm]
    exact h3
