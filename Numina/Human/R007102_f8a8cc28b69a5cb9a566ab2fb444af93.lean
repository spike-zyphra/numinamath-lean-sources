import Mathlib

/-The product of positive integers $x$, $y$ and $z$ equals 2004. What is the minimum possible value of the sum $x + y + z$?-/
theorem number_theory_12400 :
  IsLeast {n | ∃ x y z : ℕ, x * y * z = 2004 ∧ n = x + y + z} 174 := by
    constructor
    · simp
      use 167, 4, 3
    · intro n hn
      simp at hn
      obtain ⟨a, b, c, c1, c2⟩ := hn
      -- Prime factorize $2004=2^2\cdot 3\cdot 167$
      -- So one of a b c will divided by 167.
      have dvdabc : 167 ∣ a ∨ 167 ∣ b ∨ 167 ∣ c := by
        have : 167 ∣ a * b * c := c1 ▸ (by norm_num)
        rcases (Nat.Prime.dvd_mul (by norm_num)).1 this with dvdab | dvdc
        · rcases (Nat.Prime.dvd_mul (by norm_num)).1 dvdab with dvda | dvdb <;> tauto
        · tauto
      -- auxiliary lemma : if $a$ is divided by 167, then 174 ≤ n
      have aux {a b c : ℕ} (h1 : a * b * c = 2004) (hn : n = a + b + c)
      (hdvd : 167 ∣ a) : 174 ≤ n := by
        by_cases a167 : a = 167
        · have hbc : b * c = 12 := by simp [a167] at h1; linarith
          rw [hn, a167]
          -- The other two summands multiply to give 12, and the minimum sum of two positive integers that multiply to give 12 is $4+3=7$.  Therefore, the minimum value of $x+y+z$ is $167+4+3=\boxed{174}$.
          have : 7 ≤ b + c := by
            have : b ≤ 12 := Nat.le_of_dvd (by omega) (Dvd.intro _ hbc)
            have : c ≤ 12 := Nat.le_of_dvd (by omega) (Dvd.intro_left _ hbc)
            interval_cases b <;> (interval_cases c <;> aesop) <;> linarith
          linarith
        · have : 2 * 167 ≤ a := by
            obtain ⟨t, ht⟩ := hdvd
            have : t ≠ 0 := fun t0 => by simp [t0] at ht; simp [ht] at h1
            have : t ≠ 1 := fun t1 => by simp [t1] at ht; simp [ht] at a167
            omega
          linarith
      -- Since a b c has rotation symmetry，so we can use the above lemma on b and c. Then we get the same conclusion.
      have c1' : b * a * c = 2004 := by linarith
      have c2' : n = b + a + c := by linarith
      have c1'' : c * b * a = 2004 := by linarith
      have c2'' : n = c + b + a := by linarith
      rcases dvdabc with dvda | dvdb | dvdc
      · exact aux c1 c2 dvda
      · exact aux c1' c2' dvdb
      · exact aux c1'' c2'' dvdc
