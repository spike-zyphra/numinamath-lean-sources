import Mathlib

/-Let $A$ and $B$ be integers. Consider the following system of linear Diophantine equations:

1) $x+y+z+w=A$
2) $x+2y+3z+4w=B$
3) $x+4y+9z+16w=1000$

Show that if $B$ is odd, there are no integer solutions $(x,y,z,w)$.
If $B$ is even, show that the complete set of integer solutions is given by taking $w=n$ for any integer $n$, and then

$z = \frac{1000-3B+2A}{2} - 3n$
$y = -3A+4B-1000+3n$
$x = \frac{6A-5B+1000}{2} - n$-/

theorem number_theory_639745 (x y z w A B: ℤ):
  (x + y + z + w = A) ∧ (x + 2 * y + 3 * z + 4 * w = B) ∧ (x + 4 * y + 9 * z + 16 * w = 1000) ↔
  Even B ∧ ∃ n, x = (6 * A - 5 * B + 1000) / 2 - n ∧ y = -3 * A + 4 * B - 1000 + 3 * n ∧
  z = (1000 - 3 * B + 2 * A) / 2 - 3 * n ∧ w = n := by

  constructor

  -- the forward direction
  .
    intro h
    rcases h with ⟨h1, h2, h3⟩
    -- we first show that B must be even
    have u: Even B := by
      -- to see this, we express B in the form of 2 * ?
      have f1: 3 * B = 1000 + 2 * A - (2 * z + 6 * w):= by
        nlinarith
      have v: 2 ∣ 3 * B := by
        rw [f1]
        rw [show 1000 + 2 * A - (2 * z + 6 * w) = 2 * (500 + A - z - 3 * w) by ring]
        simp
      by_contra! g
      simp at g
      apply Odd.exists_bit1 at g
      obtain ⟨k, hk⟩ := g
      simp [hk] at v
      have c: 2 ∣ 3 := by
        zify
        rw [show 3 = 3 * (2 * k + 1) - 2 * (3 * k) by ring]
        apply Int.dvd_sub
        .
          tauto
        .
          simp
      norm_num at c
    simp [u]
    rw [even_iff_exists_two_mul] at u
    obtain ⟨s, hs⟩ := u
    simp [hs] at *

    -- then we just take n to be w
    use w
    -- for the rest, we compute x y z separately
    constructor
    -- compute x
    .
      suffices 2 * x = (6 * A - 5 * (2 * s) + 1000) - 2 * w by
        qify at this
        qify
        have u: ↑((6 * A - 5 * (2 * s) + 1000) / 2) = ((6 * A - 5 * (2 * s) + 1000): ℚ) / 2 := by
          rw [Rat.intCast_div]
          qify
          rw [show 6 * A - 5 * (2 * s) + 1000 = 2 * (3 * A - 5 * s + 500) by ring]
          simp
        rw [u]
        linarith
      nlinarith
    .
      constructor
      -- compute y
      .
        nlinarith
      -- compute z
      .
        simp
        suffices 2 * z = (1000 - 3 * (2 * s) + 2 * A) - 6 * w by
          qify at this
          qify
          have u: ↑((1000 - 3 * (2 * s) + 2 * A) / 2) = ((1000 - 3 * (2 * s) + 2 * A): ℚ) / 2 := by
            rw [Rat.intCast_div]
            qify
            rw [show 1000 - 3 * (2 * s) + 2 * A = 2 * (500 - (3 * s) + A) by ring]
            simp
          rw [u]
          linarith
        nlinarith


  -- the backward direction, show that the above expressions are indeed solutions
  .
    intro h
    rcases h with ⟨hb, h⟩
    rw [even_iff_exists_two_mul] at hb
    obtain ⟨s, hs⟩ := hb
    simp [hs] at *
    obtain ⟨n, h1, h2, h3, h4⟩ := h
    -- for convenience, we write in the form of ℚ
    qify at *
    -- to do this, we have to tackle with the fractions
    have u: ↑((6 * A - 5 * (2 * s) + 1000) / 2) = ((6 * A - 5 * (2 * s) + 1000): ℚ) / 2 := by
      rw [Rat.intCast_div]
      qify
      rw [show 6 * A - 5 * (2 * s) + 1000 = 2 * (3 * A - 5 * s + 500) by ring]
      simp
    have v: ↑((1000 - 3 * (2 * s) + 2 * A) / 2) = ((1000 - 3 * (2 * s) + 2 * A): ℚ) / 2 := by
      rw [Rat.intCast_div]
      qify
      rw [show 1000 - 3 * (2 * s) + 2 * A = 2 * (500 - (3 * s) + A) by ring]
      simp
    simp [u, v] at h1 h3
    clear u v
    constructor
    .
      nlinarith
    .
      constructor
      .
        nlinarith
      .
        nlinarith
