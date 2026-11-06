import Mathlib

/-
Let $K$ be a positive integer. Let $r = 1/K$. Show that for all integers $m, n$ which are multiples of $K$ (i.e., $m, n \in K\mathbb{Z}$), if $m$ divides $n$, then $\lfloor mr \rfloor$ divides $\lfloor nr \rfloor$.
-/

theorem number_theory_635100 (K:ℤ) (Kpos: 0 < K) (r:ℝ) (hr: r = 1/(K:ℝ)) (m n : ℤ) (hm: K ∣ m) (hn: K ∣ n) (hmn: m ∣ n) : ⌊m*r⌋ ∣ ⌊n*r⌋ := by 
  obtain ⟨dm,hm⟩ := hm
  obtain ⟨dn,hn⟩ := hn
  rw [hr,hm,hn]
  field_simp

  obtain ⟨dmn,hmn⟩ := hmn
  rw [hmn, hm] at hn
  use dmn
  nlinarith
  