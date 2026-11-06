import Mathlib

/- 3. Let the lengths of all sides of a right-angled triangle be natural numbers. Prove that the length of at least one side is a number divisible by 5. -/
theorem number_theory_195666 (a b c : ℕ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) :
    5 ∣ a ∨ 5 ∣ b ∨ 5 ∣ c := by
  -- first convert the goals to 5 dividing the squares
  have h_5_dvd_sq (n : ℕ) : 5 ∣ n ↔ 5 ∣ n^2 := by
    refine Iff.symm (Prime.dvd_pow_iff_dvd ?_ (by norm_num))
    rw [← Nat.prime_iff]
    norm_num
  rw [h_5_dvd_sq a, h_5_dvd_sq b, h_5_dvd_sq c]
  -- next convert to modular arithemtic
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_zmod_eq_zero_iff_dvd]
  have h : (a : ZMod 5)^2 + (b: ZMod 5)^2 = (c: ZMod 5)^2 := by
    norm_cast
    rw [h''']
  -- we'll prove by contradiction
  by_contra hc
  push_neg at hc
  push_cast at hc
  obtain ⟨ha, hb, hc⟩ := hc
  clear * - h ha hb hc
  -- for any x in mod 5, x^2 = 0, 1 or 4
  have h_sq_mod_5 (x: ZMod 5) : x^2 = 0 ∨ x^2 = 1 ∨ x ^2 = 4 := by
    fin_cases x
    all_goals simp
    all_goals norm_cast
  -- the square are not 0 mod 5, so they are 1 or 4
  have ha := Or.resolve_left (h_sq_mod_5 (a:ZMod 5)) ha
  have hb := Or.resolve_left (h_sq_mod_5 (b:ZMod 5)) hb
  have hc := Or.resolve_left (h_sq_mod_5 (c:ZMod 5)) hc
  -- now case work thorough all possibilities to see all are false
  obtain ha | ha := ha <;> obtain hb | hb := hb <;> obtain hc | hc := hc
  all_goals (rw [ha, hb, hc] at h; norm_cast at h)