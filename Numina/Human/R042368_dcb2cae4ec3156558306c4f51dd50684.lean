import Mathlib

/-Alice thinks of four positive integers a≤b≤c≤d satisfying {ab+cd,ac+bd,ad+bc} = {40,70,100}
.What are all the possible tuples (a,b,c,d) that  Alice could be thinking of?-/
theorem algebra_610543:{(a,b,c,d): ℤ × ℤ × ℤ × ℤ | 0 < a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
 {a * b + c * d, a * c + b * d, a * d + b * c} = ({40,70,100}: Set ℤ)} = {((1: ℤ),(4: ℤ),(6: ℤ),(16: ℤ))} := by
  ext ⟨a,b,c,d⟩
  simp
  constructor
  -- the fowrard direction
  . intro h
    rcases h with ⟨ha,hab,hbc,hcd,h⟩
    -- we first prove the order in the set
       -- a * c + b * d < a * b + c * d
    have id1: a * b + c * d - (a * c + b * d) = (c - b) * (d - a) := by ring
    have ineq1: 0 ≤ a * b + c * d - (a * c + b * d) := by
      rw [id1]
      nlinarith
    have ne1: a * b + c * d - (a * c + b * d) ≠ 0 := by
      by_contra! no
      rw [id1] at no
      simp at no
      rcases no with l | l
      . replace l: b = c := by omega
        simp [l] at h
        have l:  ({a * c + c * d, a * d + c * c}: Set ℤ).ncard = 3 := by
          rw [h]
          simp
        by_cases f: a * c + c * d ≠ a * d + c * c
        . have g: ({a * c + c * d, a * d + c * c}: Set ℤ).ncard = 2 := by
            rw [Set.ncard_eq_two]
            use a * c + c * d
            use a * d + c * c
          rw [g] at l
          tauto
        . simp at f
          simp [f] at l
      . replace l: a = d := by omega
        simp [l] at h
        have l2: b = d := by omega
        have l3: c = d := by omega
        simp [l2,l3] at *
        have r:  ({d * d + d * d}: Set ℤ).ncard = 3 := by
          rw [h]
          simp
        have s: ({d * d + d * d}: Set ℤ).ncard = 1 := by
          rw [Set.ncard_eq_one]
          use d * d + d * d
        rw [r] at s
        tauto
    replace ineq1: a * c + b * d < a * b + c * d := by omega
    clear ne1
       -- a * d + b * c < a * c + b * d
    have id2: a * c + b * d - (a * d + b * c) = (b - a) * (d - c) := by ring
    have ineq2: 0 ≤ a * c + b * d - (a * d + b * c) := by
      rw [id2]
      nlinarith
    have ne2: a * c + b * d ≠ (a * d + b * c) := by
      by_contra! no
      simp [no] at h
      have l:  ({a * b + c * d, a * d + b * c}: Set ℤ).ncard = 3 := by
         rw [h]
         simp
      by_cases f: a * b + c * d ≠ a * d + b * c
      . have g: ({a * b + c * d, a * d + b * c}: Set ℤ).ncard = 2 := by
          rw [Set.ncard_eq_two]
          use a * b + c * d
          use a * d + b * c
        rw [g] at l
        tauto
      . simp at f
        simp [f] at l
    replace ineq2: a * d + b * c < a * c + b * d := by omega
    clear ne2

    -- Then we give the value of expression in the set
    have eq1: a * d + b * c = 40 := by
      have l: a * d + b * c ∈ ({40,70,100}: Set ℤ) := by
        rw [← h]
        simp
      simp at l
      rcases l with l | l | l
      . exact l
      . simp [l] at h
        rw [l] at ineq2
        have o: a * c + b * d ∈ ({40,70,100}: Set ℤ) := by
          rw [← h]
          simp
        simp at o
        rcases o with o | o | o
        . linarith
        . linarith
        . rw [o] at ineq1
          have p: a * b + c * d ∈ ({40,70,100}: Set ℤ) := by
            rw [← h]
            simp
          simp at p
          rcases p with p | p | p
          all_goals linarith
      . simp [l] at h
        rw [l] at ineq2
        have o: a * c + b * d ∈ ({40,70,100}: Set ℤ) := by
          rw [← h]
          simp
        simp at o
        rcases o with o | o | o
        . linarith
        . linarith
        . rw [o] at ineq1
          have p: a * b + c * d ∈ ({40,70,100}: Set ℤ) := by
            rw [← h]
            simp
          simp at p
          rcases p with p | p | p
          all_goals linarith
    simp [eq1] at h
    have eq2: a * c + b * d = 70 := by
      have l: a * c + b * d ∈ ({40,70,100}: Set ℤ) := by
        rw [← h]
        simp
      simp at l
      rcases l with l | l | l
      . linarith
      . exact l
      . have p: a * b + c * d ∈ ({40,70,100}: Set ℤ) := by
          rw [← h]
          simp
        simp at p
        rcases p with p | p | p
        . linarith
        . linarith
        . linarith
    simp [eq2] at h
    have eq3: a * b + c * d = 100 := by
      have l: a * b + c * d ∈ ({40,70,100}: Set ℤ) := by
        rw [← h]
        simp
      simp at l
      rcases l with l | l | l
      . linarith
      . linarith
      . exact l
    clear h ineq1 ineq2

    -- now we can find value of a b c d
    simp [eq1,eq2,eq3] at id1 id2
    have ineq: c - b ≤ d - a := by omega
    have dvd: c - b ∣ 30 := by rw [id1]; apply Int.dvd_mul_right
    have ld: c - b ≤ 5 := by nlinarith
    have o: 0 < c - b := by
      by_contra! o
      replace o: c = b := by omega
      rw [o] at id1
      simp at id1
    have l: c - b = 1 ∨ c - b = 2 ∨ c - b = 3 ∨ c - b = 4 ∨ c - b = 5 := by omega
    rcases l with l | l | l | l | l
    . clear ld o dvd
      simp [l] at id1
      clear ineq
      replace l: c = b + 1 := by omega
      replace id1: d = a + 30 := by omega
      simp [l,id1] at *
      clear hbc l id1
      ring_nf at eq1
      have la: a = 1 := by nlinarith
      simp [la] at *
      nlinarith
    . clear ld o dvd
      simp [l] at id1
      clear ineq
      replace l: c = b + 2 := by omega
      replace id1: d = a + 15 := by omega
      simp [l,id1] at *
      clear hbc l id1
      ring_nf at eq1
      have la: a = 1 := by nlinarith
      simp [la] at *
      ring_nf at eq3
      have lb: b = 4 := by nlinarith
      simp [lb]
    . clear ld o dvd
      simp [l] at id1
      clear ineq
      replace l: c = b + 3 := by omega
      replace id1: d = a + 10 := by omega
      simp [l,id1] at *
      clear hbc l id1
      ring_nf at eq1
      have la: a = 1 := by nlinarith
      simp [la] at *
      ring_nf at eq3
      have lb: b = 4 := by nlinarith
      simp [lb] at eq3
    . rw [l] at dvd
      tauto
    . clear ld o dvd
      simp [l] at id1
      clear ineq
      replace l: c = b + 5 := by omega
      replace id1: d = a + 6 := by omega
      simp [l,id1] at *
      clear hbc l id1
      ring_nf at eq1
      have la: a = 1 := by nlinarith
      simp [la] at *
      ring_nf at eq3
      have lb: b = 4 := by nlinarith
      simp [lb] at eq3

  -- the backward direction
  . intro h
    simp [h]
    apply Set.ext
    intro x
    simp
    omega
