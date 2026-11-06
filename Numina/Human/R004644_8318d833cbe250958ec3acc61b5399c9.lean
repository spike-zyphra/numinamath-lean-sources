import Mathlib

/- 25. If $b^{2}-n^{2}=a^{2}-k^{2}=c^{2}-m^{2}$, then the following equality holds:


$$

\frac{b m-c n}{a-k}+\frac{c k-a m}{b-n}+\frac{a n-b k}{c-m}=0

$$


Prove.

78 -/
theorem algebra_292736 {a b c k m n : ℝ} (h : ∃ x, b^2 - n^2 = x ∧ a^2 - k^2 = x ∧ c^2 - m^2 = x) (hbn : b - n ≠ 0) (hak : a - k ≠ 0) (hcm: c - m ≠ 0) :
    (b * m - c * n) / (a - k) + (c * k - a * m) / (b - n) + (a * n - b * k) / (c - m) = 0 := by
  obtain ⟨x, hxbn, hxak, hxcm⟩ := h
  -- rewrite using squre minus square formula
  have hxbn : (b-n)*(b+n) = x := by rw [← hxbn]; ring
  have hxak : (a-k)*(a+k) = x := by rw [← hxak]; ring
  have hxcm : (c-m)*(c+m) = x := by rw [← hxcm]; ring
  -- work by cases on b+n = 0 or not
  obtain hbnz | hbnz := @or_not (b+n = 0)
    -- if is 0, that means x = 0 and that means b+n=a+k=c+m=0
  . have hxz: x = 0 := by
      rw [hbnz] at hxbn
      simp at hxbn
      rw [hxbn]
    subst hxz
    simp [hak] at hxak
    simp [hcm] at hxcm
    -- so b = -n, a = -k, c = -m, rewrite and everything cancels out to get 0
    have hb: b = -n := by linarith
    have ha: a = -k := by linarith
    have hc: c = -m := by linarith
    rw [ha, hb, hc]
    ring
    -- if b+n ≠ 0, then x ≠ 0 and so that means a+k ≠ 0, c+m ≠ 0
  . have hakz : a + k ≠ 0 := by
      by_contra hakz
      rw [hakz] at hxak
      simp at hxak
      rw [← hxak] at hxbn
      simp [hbn, hbnz] at hxbn
    have hcmz : c + m ≠ 0 := by
      by_contra hcmz
      rw [hcmz] at hxcm
      simp at hxcm
      rw [← hxcm] at hxbn
      simp [hbn, hbnz] at hxbn
    -- now multiply each of the fractions by a+k, b+n, c+m and numerators cancel out.
    calc
      (b * m - c * n) / (a - k) + (c * k - a * m) / (b - n) + (a * n - b * k) / (c - m) = (b * m - c * n) * (a+k) / ((a - k)*(a+k)) + (c * k - a * m)*(b+n) / ((b - n)*(b+n)) + (a * n - b * k)*(c+m) / ((c - m)*(c+m)) := by
        congr 1; congr 1; all_goals (field_simp; ring)
      _ = (b*m-c*n) * (a+k) / x + (c*k-a*m)*(b+n) / x + (a*n-b*k)*(c+m) / x := by rw [hxbn, hxak, hxcm]
      _ = 0 := by
        ring_nf