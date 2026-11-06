import Mathlib

open Finset Real Nat

/-How many pairs of integers (x,y) are there such that
∣x^2−2y^2∣≤1 and∣3x−4y∣≤1 ?-/

theorem number_theory_610011: {(x, y): ℤ × ℤ | (|x ^ 2 - 2 * (y ^ 2)| ≤ 1) ∧ (|3 * x - 4 * y| ≤ 1)}.encard = 7 := by
  -- We firstly consider the casePostive x --
  have caseP: ∀ x y: ℤ, (x ≥ 0) ∧ (|x ^ 2 - 2 * (y ^ 2)| ≤ 1) ∧  (|3 * x - 4 * y| ≤ 1) →
  (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = 3 ∧  y = 2) ∨ (x = 7 ∧ y = 5) := by
    intro x y
    intro h
    rcases h with ⟨hx, h1, h2⟩
    let q:= x / 4
    let r:= x % 4
    have hq: x = 4 * q + r := by simp [q,r];omega
    have hr: r ∈ Icc 0 3:= by
      simp
      omega
    simp [Int.abs_le_one_iff] at h1 h2
    clear_value r
    fin_cases hr
    -- classify with x % 4 --
    -- x % 4 = 0 --
    . simp at hq
      simp [hq] at *
      clear hq
      left
      -- classify with h2 --
      rcases h2 with l | l | l
      . replace l: y = 3 * q := by omega
        simp [l] at h1
        have t: q ^ 2 ≤ 1 := by
          ring_nf at h1
        -- classify with h1 --
          rcases h1 with i | i | i
          . omega
          . omega
          . omega
        by_cases hq: q = 0
        . rw [hq] at l
          simp at l
          omega
        . have hq1: q = 1 := by simp [Int.abs_le_one_iff] at t; omega
          rw [hq1] at l
          simp at l
          ring_nf at h1
          rw [hq1] at h1
          omega
      . rw [show 3 * (4 * q) - 4 * y = 4 * (3 * q - y) by ring] at l
        have dvd: 4 ∣ 4 * (3 * q - y) := by
          apply dvd_mul_right
        rw [l] at dvd
        tauto
      . rw [show 3 * (4 * q) - 4 * y = 4 * (3 * q - y) by ring] at l
        have dvd: 4 ∣ 4 * (3 * q - y) := by
          apply dvd_mul_right
        rw [l] at dvd
        tauto
    -- x % 4 = 1 --
    . simp at hq
      simp [hq] at h2
      ring_nf at h2
      have hy: y = 3 * q + 1 := by
        omega
      clear h2
      simp [hy,hq] at h1
      ring_nf at h1
      replace hx: q ≥ 0 := by omega
      rcases h1 with i | i | i
      . omega
      . have no: -1 + (-(q * 4) - q ^ 2 * 2) ≤ 0 := by
          simp [hx]
          calc
            -(q * 4) ≤ 0 := by omega
                    _≤ 1 := by omega
                    _≤ 1 +  q ^ 2 * 2 := by nlinarith
        rw [i] at no
        tauto
      . simp at i
        have q_val: q = 0 := by
          rw [show -(q * 4) - q ^ 2 * 2 = -q * (4 + 2 * q) by ring] at i
          simp at i
          omega
        rw [q_val] at hy
        simp at hy
        rw [q_val] at hq
        simp at hq
        omega
    -- x % 4 = 2 --
    . simp at hq
      simp [hq] at h2
      ring_nf at h2
      rcases h2 with l | l | l
      . replace l: 6 = 4 * (y - 3 * q) := by omega
        have dvd: 4 ∣ 4 * (y - 3 * q) := by
          apply dvd_mul_right
        rw [← l] at dvd
        tauto
      . replace l: 5 = 4 * (y - 3 * q) := by omega
        have dvd: 4 ∣ 4 * (y - 3 * q) := by
          apply dvd_mul_right
        rw [← l] at dvd
        tauto
      . replace l: 7 = 4 * (y - 3 * q) := by omega
        have dvd: 4 ∣ 4 * (y - 3 * q) := by
          apply dvd_mul_right
        rw [← l] at dvd
        tauto
    -- x % 4 = 3 --
    . simp at hq
      simp [hq] at h2
      ring_nf at h2
      rcases h2 with l | l | l
      . replace l: 9 = 4 * (y - 3 * q) := by omega
        have dvd: 4 ∣ 4 * (y - 3 * q) := by
          apply dvd_mul_right
        rw [← l] at dvd
        tauto
      . replace l: 8 = 4 * (y - 3 * q) := by omega
        replace l: 2 = y - 3 * q := by omega
        replace l: y = 3 * q + 2 := by omega
        simp [l,hq] at h1
        ring_nf at h1
        rcases h1 with i | i | i
        . omega
        . have q_val: q = 0 := by
            replace i: q ^ 2 * 2 = 0 := by omega
            simp at i
            omega
          simp [q_val] at hq l
          tauto
        . replace hx: q ≥ 0 := by omega
          replace i: q ^ 2 = 1 := by omega
          simp at i
          have q_val: q = 1 := by omega
          simp [q_val] at hq l
          tauto
      . replace l: 10 = 4 * (y - 3 * q) := by omega
        have dvd: 4 ∣ 4 * (y - 3 * q) := by
          apply dvd_mul_right
        rw [← l] at dvd
        tauto
  have set_eq: {(x, y): ℤ × ℤ | (|x ^ 2 - 2 * (y ^ 2)| ≤ 1) ∧ (|3 * x - 4 * y| ≤ 1)} = {0,1,(-1,-1),(3,2),(-3,-2),(7,5),(-7,-5)} := by
    . ext ⟨x,y⟩
      simp
      constructor
      . intro h
        rcases h with ⟨h1,h2⟩
        by_cases h3: x ≥ 0
        . specialize caseP x y
          simp [h1,h2,h3] at caseP
          tauto
        -- for the case x < 0, we can use the symmetry of the equation,i.e. make use of -x and -y --
        . let a:= -x
          let b:= -y
          have aP: a ≥ 0 := by omega
          have ha: x = -a := by omega
          have hb: y = -b := by omega
          simp [ha,hb] at h1 h2
          have eq: |-(3 * a) + 4 * b| = |3 * a - 4 * b| := by
            calc
              |-(3 * a) + 4 * b| = |-((3 * a) - 4 * b)| := by ring_nf
                               _ = |3 * a - 4 * b| := by apply abs_neg
          rw [eq] at h2
          specialize caseP a b
          simp [aP,h1,h2] at caseP
          simp [ha,hb]
          clear * - caseP
          clear_value a b
          tauto
      . intro h
        rcases h with h | h | h | h | h | h | h
        all_goals simp [h]
  simp [set_eq]
  simp [Set.encard]
  have count : Finset.card ({0,1, (-1,-1), (3,2), (-3,-2), (7,5), (-7,-5)} : Finset (ℤ × ℤ)) = 7 := by
    -- First, prove that each new element is not in the remaining set
    have h1 : 1 ∉ ({0} : Finset (ℤ × ℤ)) := by decide
    have h_1 : (-1,-1) ∉ ({0, 1} : Finset (ℤ × ℤ)) := by decide
    have h3 : (3,2) ∉ ({0, 1, (-1,-1)} : Finset (ℤ × ℤ)) := by decide
    have h_3 : (-3,-2) ∉ ({0, 1, (-1,-1), (3,2)} : Finset (ℤ × ℤ)) := by decide
    have h7 : (7,5) ∉ ({0, 1, (-1,-1), (3,2), (-3,-2)} : Finset (ℤ × ℤ)) := by decide
    have h_7 : (-7,-5) ∉ ({0, 1, (-1,-1), (3,2), (-3,-2), (7,5)} : Finset (ℤ × ℤ)) := by decide
    -- Now simplify the cardinality using insertion rules
    apply Finset.card_insert_of_not_mem h_7
  simp [count]