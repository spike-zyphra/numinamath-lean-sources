import Mathlib

open Finset

set_option maxHeartbeats 5000000

/- Let $a < b < c$ be three positive integers. Prove that among any $2 c$ consecutive positive integers there exist three different numbers $x, y, z$ such that $a b c$ divides $x y z$. -/
theorem number_theory_241515 (a b c : ℕ) (ha : 0 < a) (hb : a < b) (hc : b < c)
    : (∀ n, ∃ x y z, x ∈ Finset.Icc n (n + 2 * c - 1) ∧ y ∈ Finset.Icc n (n + 2 * c - 1) ∧
      z ∈ Finset.Icc n (n + 2 * c - 1) ∧ x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ a * b * c ∣ x * y * z) := by
    intro n

    -- for any c consective numbers, there's a number divisible by c
    have h1: ∀ n c, c>0 →  ∃ z, z ∈ Finset.Icc (n) (n+c-1)∧ c ∣ z := by
      intro n c hc
      let q := n/c
      let r := n%c
      have h : n = r + c * q  := by rw [Nat.mod_add_div]
      by_cases h3: r = 0
      . use n
        constructor
        . simp
          rw [Nat.le_sub_one_iff_lt]
          all_goals nlinarith
        . simp [h3] at h
          rw [h]
          apply Nat.dvd_mul_right
      . use c*(q+1)
        constructor
        . simp [Nat.ne_zero_iff_zero_lt] at h3
          simp
          rw [mul_add, mul_one, h]
          constructor
          . have : r < c := by apply Nat.mod_lt ; nlinarith
            nlinarith
          . omega
        . simp [h3] at h
          apply Nat.dvd_mul_right

    -- among any b consecutive numbers, there are two different numbers x and y such that ab divides xy
    have h2: ∃ x y, x ∈ Finset.Icc n (n+b-1) ∧ y ∈ Finset.Icc n (n+b-1)∧x≠y∧a*b∣x*y := by
      let ⟨x', ⟨hx'1, hx'2⟩ ⟩ := h1 n b (by nlinarith)
      let ⟨y', ⟨hy'1, hy'2⟩ ⟩ := h1 n a (by nlinarith)
      simp at hx'1 hy'1
      by_cases h3: x' = y'
      . -- in case x' = y', let e be the lcm of a and b
        let e := a.lcm b
        -- d be the gcd of a and b
        let d := a.gcd b
        -- we have e ∣ x' from a ∣ x' ∧ b ∣ x'
        have h4: e ∣ x' := by
          unfold e
          apply Nat.lcm_dvd
          . rw [h3]
            exact hy'2
          . exact hx'2

        -- we have d ≤ b / 2 from d ∣ b and d < b
        have h5: d ≤ b / 2 := by
          have h5_1: d ∣ b := by
            unfold d
            exact Nat.gcd_dvd_right a b
          have h5_2: d < b := by
            calc d ≤ a := by
                  unfold d
                  exact Nat.gcd_le_left b ha
            _ < b := by exact hb
          cases' h5_1 with k hk
          have : k > 1 := by
            apply Nat.lt_of_le_of_ne
            . nlinarith
            . intro h
              rw [←h] at hk
              nlinarith
          have hk': k ≥ 2 := by nlinarith
          rw [hk, Nat.le_div_iff_mul_le]
          all_goals nlinarith

        have h6: 0 < d := by exact Nat.gcd_pos_of_pos_left b ha

        -- We have ab=de
        rw [show a*b = d*e by simp [e, d, Nat.gcd_mul_lcm]]

        -- we split case and find z' in another b/2 consecutive numbers with d ∣ z', where ab ∣ x'z'
        by_cases h7: x' < n + b/2
        . let ⟨z', ⟨hz'1, hz'2⟩⟩  := h1 (n+b/2) d h6
          use x', z'
          simp only [mem_Icc] at hz'1
          and_intros
          . simp
            exact hx'1
          . simp
            constructor
            . nlinarith
            . omega
          . nlinarith
          . rw [mul_comm d e]
            exact Nat.mul_dvd_mul h4 hz'2
        . let ⟨z', ⟨hz'1, hz'2⟩⟩  := h1 n d h6
          use x', z'
          simp only [mem_Icc] at hz'1
          and_intros
          . simp
            exact hx'1
          . simp
            constructor
            . nlinarith
            . omega
          . omega
          . rw [mul_comm d e]
            exact Nat.mul_dvd_mul h4 hz'2
      . -- in case that x'≠y', we can just use x' and y'
        use x', y'
        and_intros
        . simp;
          constructor; all_goals nlinarith
        . simp
          constructor;
          . nlinarith
          omega
        . exact h3
        rw [mul_comm a b]
        exact Nat.mul_dvd_mul hx'2 hy'2

    have h3: n+b-1 < n+c := by
      calc n+b-1 < n+b := by simp; apply Or.intro_right; nlinarith
      _ < n+c := by nlinarith

    -- Now divide the 2c consecutive numbers into two groups of c consecutive nubmers, the first group we can find distinct x and y such as ab ∣ xy
    let ⟨x, y, ⟨hx, hy, hxy, habxy⟩ ⟩  := h2
    -- In second group contains a number z such that c ∣ z
    let ⟨z, ⟨hz, hcz⟩ ⟩  := h1 (n+c) c (by nlinarith)

    use x,y,z
    simp at hx hy hz
    rw [show n + c + c - 1 = n+2*c-1 by rw [two_mul, ← add_assoc]] at hz
    and_intros
    . -- where x in Icc n (n+2c-1)
      simp only [mem_Icc]
      constructor ; all_goals nlinarith
    . -- where y in Icc n (n+2c-1)
      simp only [mem_Icc]
      constructor ; all_goals nlinarith
    . -- where z in Icc n (n+2c-1)
      simp
      constructor ; all_goals nlinarith
    . -- where x≠y
      exact hxy
    . -- where y≠z
      have: y < z := by
        calc y ≤ n + b - 1 := by exact hy.2
        _ < n + c := by exact h3
        _ ≤ z := by exact hz.1
      nlinarith
    . -- where z≠x
      have: x < z := by
        calc x ≤ n + b - 1 := by exact hx.2
        _ < n + c := by exact h3
        _ ≤ z := by exact hz.1
      nlinarith
    . -- abc ∣ xyz
      apply Nat.mul_dvd_mul
      . exact habxy
      . exact hcz
