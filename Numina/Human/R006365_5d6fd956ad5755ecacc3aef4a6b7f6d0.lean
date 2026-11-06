import Mathlib

/-
Let $S_0$ be a positive integer that is a multiple of 99. Let $K_0 = S_0/99$.
Suppose Grandma's age $G$ and granddaughter's age $D$ satisfy the following conditions:
1. Grandma is not yet 100 years old ($G < 100$).
2. The granddaughter is more than 10 years old ($D > 10$).
3. Grandma's age $G$ is a multiple of the granddaughter's age $D$.
4. When Grandma's age $G$ is written down followed by the granddaughter's age $D$, a four-digit number $N_1$ is formed. When the granddaughter's age $D$ is written down followed by Grandma's age $G$, a different four-digit number $N_2$ is formed. (These numbers are formed by concatenation, so $N_1 = 100G + D$ and $N_2 = 100D + G$. The four-digit requirement implies that $G$ and $D$ must both be two-digit numbers. Thus $10 \le G \le 99$ and, combined with $D>10$, $11 \le D \le 99$.)
5. The difference between these two four-digit numbers, $N_1 - N_2$, is equal to $S_0$.

Determine the set of all possible pairs of ages $(G,D)$. Show that this set is equal to all pairs $(d+K_0, d)$ where $d$ is an integer such that $d$ is a divisor of $K_0$, $11 \le d$, and $d+K_0 \le 99$.
-/

theorem number_theory_636283 (S0 K0: ℤ) (h0: 0 < S0) (h1 : 99 ∣ S0) (h2 : K0 = S0 / 99):
{(G,D): ℤ × ℤ | G < 100 ∧ D > 10 ∧ D ∣ G ∧ 10 ≤ G ∧ D < 99 ∧ (100*G+D) - (100*D+G) = S0} = {(x,y): ℤ × ℤ | x = y + K0 ∧ y ∣ K0 ∧ 11 ≤ y ∧ x ≤ 99} := by
  
  --We simply check every property separately.
  ext ⟨x,y⟩
  simp
  constructor<;> intro h

  obtain ⟨xl,yg,ydm,xg,yl,h⟩ := h
  ring_nf at h
  have eq: x - y = K0 := by omega
  constructor
  omega
  constructor
  obtain ⟨d,hd⟩ := ydm
  use (d-1)
  rw [← eq, hd]
  ring
  constructor
  linarith
  linarith

  obtain ⟨h3,h4,h5,h6⟩ := h
  constructor
  linarith
  constructor
  linarith
  constructor
  obtain ⟨d,hd⟩ := h4
  use (d+1)
  rw [h3]
  rw [hd]
  ring
  constructor
  omega
  constructor
  omega
  ring_nf
  omega
  
