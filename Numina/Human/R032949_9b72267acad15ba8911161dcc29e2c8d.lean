import Mathlib

/- Let $a,b,c,d,e,f,g,h,i$ be distinct integers from $1$ to $9.$ The minimum possible positive value of 
$$
\dfrac{a \cdot b \cdot c - d \cdot e \cdot f}{g \cdot h \cdot i}
$$
 can be written as $\frac{m}{n},$ where $m$ and $n$ are relatively prime positive integers. Find $m+n.$ -/
theorem algebra_98619 (m n : ℕ) (hc : m.Coprime n) (hl : IsLeast {x | ∃ (a b c d e f g h i : ℚ) (hperm : List.Perm [a, b, c, d, e, f, g, h, i] [1, 2, 3, 4, 5, 6, 7, 8, 9]), (a * b * c - d * e * f) / (g * h * i) = x ∧ 0 < x} (↑m / ↑n)) (hn : n ≠ 0) : m + n = 289 := by
  have ey : IsLeast {x | ∃ (a b c d e f g h i : ℚ) (hperm : List.Perm [a, b, c, d, e, f, g, h, i] [1, 2, 3, 4, 5, 6, 7, 8, 9]), (a * b * c - d * e * f) / (g * h * i) = x ∧ 0 < x} (1 / 288) := by
    constructor
    -- witness
    · exists 2, 3, 6, 1, 5, 7, 4, 8, 9
      native_decide
    -- optimality
    · simp only [exists_prop]
      intros x ha
      simp only [Set.mem_setOf_eq] at ha
      obtain ⟨a, b, c, d, e, f, g, h, i, hh, hj, hk⟩ := ha
      rw [← List.mem_permutations] at hh
      subst x
      -- next up we have to make a list
      obtain ⟨l, hl⟩ : ∃ l, l = [a, b, c, d, e, f, g, h, i] := ⟨_, rfl⟩
      have dl : l.length = 9 := by simp [hl]
      -- we turn variables into list accesses
      have da : a = l[0]! := by simp [hl]
      have db : b = l[1]! := by simp [hl]
      have dc : c = l[2]! := by simp [hl]
      have dd : d = l[3]! := by simp [hl]
      have de : e = l[4]! := by simp [hl]
      have df : f = l[5]! := by simp [hl]
      have dg : g = l[6]! := by simp [hl]
      have dh : h = l[7]! := by simp [hl]
      have di : i = l[8]! := by simp [hl]
      rw [←hl] at hh; clear hl
      subst a b c d e f g h i
      clear hc hl hn m n
      -- it follows that $a \cdot b \cdot c$ and $d \cdot e \cdot f$ are consecutive composites with prime factors no other than $2,3,5,$ and $7.$ The smallest values for $a \cdot b \cdot c$ and $d \cdot e \cdot f$ are $36$ and $35,$ respectively.
      have imp2 : l[0]! * l[1]! * l[2]! - l[3]! * l[4]! * l[5]! ≥ 36 - 35 := by revert l hh hk; native_decide
      -- To minimize a positive fraction, we minimize its numerator and maximize its denominator. It is clear that $\frac{a \cdot b \cdot c - d \cdot e \cdot f}{g \cdot h \cdot i} \geq \frac{1}{7\cdot8\cdot9}.$
      revert l hh dl hk imp2; native_decide
  have el : (↑m : ℚ) / ↑n = 1/288 := by
    obtain ⟨g1, g2⟩ := hl
    obtain ⟨g3, g4⟩ := ey
    have := g2 g3
    have b := g4 g1
    linarith
  have := @Rat.div_int_inj m n 1 288 (by norm_num; exact Nat.zero_lt_of_ne_zero hn) (by decide) (by simp only [Int.natAbs_ofNat]; exact hc) (by decide) (by norm_num; exact el)
  linarith