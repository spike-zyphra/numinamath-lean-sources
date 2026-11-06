import Mathlib

open Nat

/- Soit $a, b, c$ et $d$ des entiers naturels non nuls.
On suppose que $a!+b!=c!+d!$. Démontrer que $a b=c d$. -/
theorem number_theory_605130 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (hd : 0 < d)
  (h : a ! + b ! = c ! + d !): a * b = c * d := by
  -- suppose without loss of generality, a ≤ b,  c ≤ d, a ≤ c
  wlog habcd: a ≤ b ∧ c ≤ d ∧ a ≤ c
  · push_neg at habcd
    by_cases h1: a ≤ b ∧ c ≤ d
    · -- swap ab,cd in this case.
      apply (this c d a b hc hd ha hb h.symm ?_).symm
      simp [h1, le_of_lt (habcd h1.left h1.right)]
    push_neg at h1
    by_cases h2: a ≤ b
    · -- swap cd
      rw [mul_comm c d]
      by_cases had: a ≤ d
      · apply this a b d c ha hb hd hc (by linarith [h])
        simp [h2, le_of_lt (h1 h2), had]
      · -- swap two sides.
        push_neg at had
        apply (this d c a b hd hc ha hb (by linarith [h]) ?_).symm
        simp [h2, le_of_lt had, le_of_lt (h1 h2)]
    -- swap ab
    push_neg at h2
    rw [mul_comm a b]
    by_cases h3: b ≤ c
    · by_cases hcd: c ≤ d
      · apply this b a c d hb ha hc hd (by linarith [h])
        simp [h3, le_of_lt h2, hcd]
      · -- swap cd
        rw [mul_comm c d]; push_neg at hcd
        by_cases hbd: b ≤ d
        · apply this b a d c hb ha hd hc (by linarith [h])
          simp [le_of_lt hcd, le_of_lt h2, hbd]
        · push_neg at hbd
          -- swap two sides.
          symm
          apply this d c b a hd hc hb ha (by linarith [h])
          simp [le_of_lt hcd, le_of_lt h2, le_of_lt hbd]
    · push_neg at h3
      -- swap two sides
      symm
      by_cases hcd: c ≤ d
      · apply this c d b a hc hd hb ha (by linarith [h])
        simp [hcd, le_of_lt h2, le_of_lt h3]
      · push_neg at hcd
        -- swap cd
        rw [mul_comm c d]
        by_cases hdb: d ≤ b
        · apply this d c b a hd hc hb ha (by linarith [h])
          simp [le_of_lt hcd, le_of_lt h2, hdb]
        · push_neg at hdb
          -- swap two sides
          symm
          apply this b a d c hb ha hd hc (by linarith [h])
          simp [le_of_lt h2, le_of_lt hcd, le_of_lt hdb]
  -- if positive x,y have x! = y!, then x=y
  have fac_inj{x y: ℕ}(xpos: 0 < x)(ypos: 0 < y)
    (h: x ! = y !): x = y := by
    by_cases hx: x = 1
    · simp [hx] at h
      have hy := factorial_eq_one.mp h.symm
      replace hy: y = 1 := by omega
      simp [hx, hy]
    · replace hx: x > 1 := by omega
      apply (factorial_inj hx).mp h
  -- if positive x,y have x! ≥ y!, then x ≥ y
  have le_of_facle{x y: ℕ}(xpos: 0 < x)(ypos: 0 < y)
    (h: x ! ≥ y !): x ≥ y := by
    by_cases hxy: x = y
    · simp [hxy]
    push_neg at hxy
    apply le_of_lt
    rw [← factorial_lt ypos]
    apply lt_of_le_of_ne h ?_
    contrapose! hxy
    apply fac_inj xpos ypos hxy.symm
  -- then b! = c!-a! + d!, b! ≥ d!, or b ≥ d
  have h1: b ≥ d := by
    have: b ! = (c !) - (a !) + (d !) := by
      have: a ! ≤ c ! := factorial_le habcd.right.right
      omega
    apply le_of_facle hb hd
    omega
  -- therefore we have a ≤ c ≤ d ≤ b
  -- c! divides c! + d! - b! = a!, so c ≤ a
  have h2: c ≤ a := by
    -- c ! ∣ c ! + d ! because c ≤ d.
    have hh1: c ! ∣ c ! + (d !) := by
      apply Nat.dvd_add_self_left.mpr ?_
      apply factorial_dvd_factorial habcd.right.left
    -- c ! ∣ b ! for c ≤ b
    have hh2: c ! ∣ b ! := factorial_dvd_factorial
      (le_trans habcd.right.left h1)
    -- thus c! divide the sub
    apply le_of_facle ha hc
    apply Nat.le_of_dvd (factorial_pos a) ?_
    rw [Nat.eq_sub_of_add_eq h]
    exact dvd_sub' hh1 hh2
  -- thus a = c, and therefore b = d.
  replace h2: a = c := le_antisymm habcd.right.right h2
  -- therefore b=d.
  have h3: b = d := by
    simp [h2] at h
    apply fac_inj hb hd h
  -- done.
  simp [h2, h3]