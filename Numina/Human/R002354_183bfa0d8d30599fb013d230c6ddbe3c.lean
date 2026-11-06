import Mathlib

/- Given two cubes $R$ and $S$ with integer sides of lengths $r$ and $s$ units respectively . If the difference between volumes of the two cubes is equal to the difference in their surface areas , then prove that $r=s$. -/
theorem algebra_88155 {r s : ℤ} (hr : r > 0) (hs : s > 0)
    (hvol : r^3 - s^3 = 6 * (r^2 - s^2)) : r = s := by
    have h1 : (r - s) * (r ^ 2 + r * s + s ^ 2 - 6 * r - 6 * s) = r^3 - s^3 - 6 * (r^2 - s^2) := by
      ring_nf
    simp [hvol] at h1
    rcases h1 with h1 | h1
    · linarith
    -- Just a bit different approach for 'only if ' part :\
    -- Let $r^2+rs+s^2-6r-6s=0$ or., $(r+s)^2 + (r-6)^2 + (s-6)^2= 72$ . 
    have h2 : (r + s) ^ 2 + (r - 6) ^ 2 + (s - 6) ^ 2 = 2 * (36 + (r ^ 2 + r * s + s ^ 2 - 6 * r - 6 * s)) := by
      ring_nf
    rw [h1,add_zero] at h2
    have h3 : (r + s) ^ 2 ≤ 2 * 36 := by
      rw [← h2] ;nlinarith
    have h4 : r ^ 2 ≤ 2 * 36 := by
      rw [← h2] ;nlinarith
    --  Thus $(r+s) \leq 8$ . Hence $r\leq 7$ , $s\leq 7$ . So $(r+s)^2 +(r-6)^2+(s-6)^2 \leq 8^2 + (7-6)^2+(7-6)^2 = 66$ , a contradiction!
    have h6 : s < 9 - r := by
      by_contra!
      have : 9 ^ 2 ≤ 2 * 36 := by
        nlinarith
      norm_num at this
    have h7 : 1 + 1 ≤ r + s := by
      apply add_le_add ;exact hr ;exact hs
    norm_num at h7
    have h8 : r ≤ 7 := by
      nlinarith
    interval_cases r
    <;> interval_cases s
    <;> linarith
    