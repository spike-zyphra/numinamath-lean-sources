import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all triplets of nonnegative integers  $(x,y,z)$
   and  $x\leq y$  such that  $x^2+y^2=3 \cdot 2016^z+77$-/
theorem number_theory_8484 :
  {(x, y, z) : ℕ × ℕ × ℕ | 0 ≤ x ∧ 0 ≤ z ∧ x ≤ y ∧ x^2 + y^2 = 3 * 2016^z + 77} =
    {(4, 8, 0), (14, 77, 1), (35, 70, 1)} := by
      ext x; simp; constructor <;> intro h
      · -- \(n^2 \equiv 0, 1, 2, 4 \pmod{7}\) for arbitary number $n$.
        have aux : ∀ x : ℕ, x ^ 2 ≡ 0 [MOD 7] ∨ x ^ 2 ≡ 1 [MOD 7]
          ∨ x ^ 2 ≡ 2 [MOD 7] ∨ x ^ 2 ≡ 4 [MOD 7] := by
            intro x
            have : x % 7 < 7 := by refine mod_lt x (by simp)
            have : x ≡ x % 7 [MOD 7] := ModEq.symm (mod_modEq x 7)
            interval_cases x % 7 <;> have := Nat.ModEq.pow 2 this <;> simp at this <;> tauto
        by_cases hx2 : x.2.2 = 0
        · -- If \(z = 0\), the equation simplifies to:
          -- \[
          -- x^2 + y^2 = 3 \cdot 2016^0 + 77 = 80
          -- \]
          simp [hx2] at h
          generalize ha : x.2.1 = a
          generalize hb : x.1 = b
          -- We need to find pairs \((x, y)\) such that \(x^2 + y^2 = 80\) and \(x \leq y\).
          -- Checking all pairs \((x, y)\) with \(x, y < 9\), we find:
          -- \[
          -- (x, y) = (4, 8)
          -- \]
          -- Thus, \((x, y, z) = (4, 8, 0)\) is one solution.
          have : a < 9 := by nlinarith
          have : b < 9 := by linarith
          rw [ha, hb] at h
          interval_cases a <;> (interval_cases b <;> aesop)
        -- For \(z \geq 1\), we analyze the equation modulo 7:
        -- \[
        -- 3 \cdot 2016^z + 77 \equiv 0 \pmod{7}
        -- \]
        -- This implies:
        -- \[
        -- x^2 + y^2 \equiv 0 \pmod{7}
        -- \]
        have : x.1^2 + x.2.1^2 ≡ 0 [MOD 7] := by
          rw [h.2]
          exact Nat.ModEq.add (modEq_zero_iff_dvd.mpr
              (dvd_mul_of_dvd_right (show 7 ∣ 2016^x.2.2 from Dvd.dvd.pow (by decide) hx2) _) )
                (show 77 ≡ 0 [MOD 7] by decide)
        -- Since \(n^2 \equiv 0, 1, 2, 4 \pmod{7}\), for \(x^2 + y^2 \equiv 0 \pmod{7}\),
        -- both \(x^2\) and \(y^2\) must be \(0 \pmod{7}\).
        have h1 : x.1^2 ≡ 0 [MOD 7] ∧ x.2.1^2 ≡ 0 [MOD 7] := by
          have h1 := aux x.1
          have h2 := aux x.2.1
          rcases h1 with h1 | h1 | h1 | h1 <;>
            (rcases aux x.2.1 with h2 | h2 | h2 | h2 <;>
              have h3 := Nat.ModEq.add h1 h2 <;> have := h3.symm.trans this <;> tauto)
        -- Therefore, \(x\) and \(y\) must be divisible by 7.
        have h2 : 7 ∣ x.1^2 ∧ 7 ∣ x.2.1^2 :=
          ⟨by convert Nat.ModEq.dvd h1.1.symm using 1; simp; norm_cast,
            by convert Nat.ModEq.dvd h1.2.symm using 1; simp; norm_cast⟩
        replace h2 : 7 ∣ x.1 ∧ 7 ∣ x.2.1 :=
          ⟨Nat.Prime.dvd_of_dvd_pow (by decide) h2.1, Nat.Prime.dvd_of_dvd_pow (by decide) h2.2⟩
        --  Let \(x = 7n\) and \(y = 7k\).
        obtain ⟨⟨n, hn⟩, k, hk⟩ := h2
        · by_cases hx2' : x.2.2 = 1
          · --  when $z = 1$, substituting these into the original equation, we get:
            -- \[
            -- 49n^2 + 49k^2 = 6125
            -- \]
            -- Simplifying, we have:
            -- \[
            -- n^2 + k^2 = 125
            -- \]
            simp [hx2', hn, hk, mul_pow] at h
            have h3 : n^2 + k^2 = 125 := by linarith
            have : k < 12 := by nlinarith
            have : n < 12 := by linarith
            have : 7 < k := by nlinarith
            -- Checking pairs \((n, k)\) such that \(n, k \leq 11\), we find:
            -- \[
            -- (n, k) = (2, 11) \text{ and } (5, 10)
            -- \]
            -- This implies:
            -- \[
            -- (x, y) = (14, 77) \text{ and } (35, 70)
            -- \]
            interval_cases k <;> (interval_cases n <;> aesop)
          · simp [hn, hk, mul_pow] at h
            -- \(49n^2 + 49k^2 \equiv 0 \pmod{49}\)
            have h1 : 49 * n ^ 2 + 49 * k ^ 2 ≡ 0 [MOD 49] :=
              Nat.ModEq.add (modEq_zero_iff_dvd.2 (by simp))
                (show 49 * k^2 ≡ 0 [MOD 49] from modEq_zero_iff_dvd.2 (by simp))
            -- For \(z \geq 2\), we check modulo 49:
            -- \[
            -- 3 \cdot 2016^2 + 77 \equiv 28 \pmod{49}
            -- \]
            --  which is a contradiction.
            have h2 : 49 * n ^ 2 + 49 * k ^ 2 ≡ 28 [MOD 49] := by
              rw [h.2]
              have : 49 ∣ 3 *  2016^x.2.2 := by
                have : 2 ≤ x.2.2 := by omega
                apply dvd_mul_of_dvd_right
                exact (show 49 ∣ 2016^2 by decide).trans (pow_dvd_pow_iff_le_right'.mpr this)
              exact Nat.ModEq.add (modEq_zero_iff_dvd.2 this) (show 77 ≡ 28 [MOD 49] by decide)
            have := h2.symm.trans h1
            exfalso; tauto
      · -- Check that $(x, y, z) = (4, 8, 0), (14, 77, 1), \text{ and } (35, 70, 1)$ are solutions.
        rcases h with h | h | h <;> simp [h]
