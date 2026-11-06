import Mathlib

open Nat Finset

/-- A cryptographer devises the following method for encoding positive integers. First, the integer
is expressed in base $5$. Second, a 1-to-1 correspondence is established between the digits that
appear in the expressions in base $5$ and the elements of the set  $\{V, W, X, Y, Z\}$. Using this
correspondence, the cryptographer finds that three consecutive integers in increasing order are
coded as $VYZ, VYX, VVW$, respectively. What is the base-$10$ expression for the integer coded as
$XYZ$?

$\textbf{(A)}\ 48 \qquad \textbf{(B)}\ 71 \qquad \textbf{(C)}\ 82 \qquad \textbf{(D)}\ 108 \qquad
\textbf{(E)}\ 113$ -/
theorem number_theory_95871 {n : ℕ} {d : ℕ →₀ ℕ}
    (hn : digits 5 n = [d 0, d 1, d 2, d 3, d 4])
    (h0 : ∀ i ∈ range 5, ∀ j ∈ range 5, d i = d j → i = j)
    (h1 : ofDigits 5 [d 0, d 1, d 4] + 1 = ofDigits 5 [d 2, d 1, d 4])
    (h2 : ofDigits 5 [d 2, d 1, d 4] + 1 = ofDigits 5 [d 3, d 4, d 4]) :
    ofDigits 5 [d 0, d 1, d 2] = 108 := by

  -- Let $n$ be the secret number. Let $n = d_4 \ d_3 \ d_2 \ d_1 \ d_0$ in base 5.
  -- For simplicity also let $V = d_4$, $W = d_3$, $X = d_2$, $Y = d_1$ and $Z = d_0$.
  let Z := d 0
  let Y := d 1
  let X := d 2
  let W := d 3
  let V := d 4

  -- By definition, each digit is between $0$ and $4$ and $V ≠ 0$.
  have d_mem (i) (hi : i ∈ range 5) : d i ∈ range 5 := by
    simp at hi ⊢
    apply Nat.digits_lt_base (m := n) (by norm_num)
    simp [hn]
    interval_cases i <;> simp

  -- Let $a$ be the number represented by the digits $V, Y, Z$ in base 5. Let $b$ be the number
  -- represented by the digits $X, Y, Z$ in base 5. Let $c$ be the number represented by the digits
  -- $W, V, V$ in base 5.
  set a := ofDigits 5 [Z, Y, V]
  set b := ofDigits 5 [X, Y, V]
  set c := ofDigits 5 [W, V, V]

  -- Therefore, we have $a = 25V + 5Y + Z$, $b = 25V + 5Y + X$ and $c = 25V + 5V + W$.
  have a_eq : a = 25 * V + 5 * Y + Z := by simp [a, ofDigits]; ring
  have b_eq : b = 25 * V + 5 * Y + X := by simp [b, ofDigits]; ring
  have c_eq : c = 25 * V + 5 * V + W := by simp [c, ofDigits]; ring

  -- By assumption $Y$ and $V$ are different.
  have Y_ne_V : Y ≠ V := by
    intro h
    have h0 := h0 1 (by simp) 4 (by simp) (by zify; linarith only [h])
    contradiction

  -- -- We are given that $b + 1 = c$. Because $c$ is larger than $b$, we must have $V < Y$.
  have Y_lt_V : Y < V := by
    by_contra! h
    replace h : V < Y := by omega
    zify at b_eq c_eq h2 h
    have h' :=
      calc (W:ℤ) = (25 * V + 5 * V + W) - (25 * V + 5 * Y + X) + 5 * (Y - V) + X := by ring
           _ = c - b + 5 * (Y - V) + X := by rw [b_eq, c_eq]
           _ = 1 + 5 * (Y - V) + X := by rw [←h2]; ring
           _ ≥ 6 := by linarith only [h]
    simp [W] at h'
    have := d_mem 3 (by norm_num)
    simp at this
    linarith only [h', this]

  -- -- We are given that $b + 1 = c$ i.e. adding $1$ causes the "fives" digit to change, we must have
  -- $X = 4$ and $W = 0$.
  have X_eq_four : X = 4 := by
    have := d_mem 2
    simp at this
    suffices h : X ≥ 4 by linarith only [this, h]
    zify at b_eq c_eq h2 ⊢
    calc (X:ℤ) = (b - c) + 5 * (V - Y) + W := by rw [b_eq, c_eq]; ring
         _ = -1 + 5 * (V - Y) + W := by rw [←h2]; ring
         _ ≥ _ := by omega

  have W_eq_zero : W = 0 := by
    have := d_mem 2
    simp at this
    suffices W ≤ 0 by linarith only [this]
    zify at b_eq c_eq h2 this ⊢
    calc (W:ℤ) = (c - b) - 5 * (V - Y) + X := by rw [b_eq, c_eq]; ring
         _ = 1 - 5 * (V - Y) + X := by rw [←h2]; ring
         _ ≤ 0 := by omega

  -- Now since $VYZ + 1 = VYX$, we have $X = Z + 1 \implies Z = 4 - 1 = 3$.
  have Z_eq_three : Z = 3 := by
    zify at b_eq a_eq h1 ⊢
    calc (Z:ℤ) = (a - b) + X := by rw [a_eq, b_eq]; ring
         _ = _ := by rw [←h1, X_eq_four]; ring

  -- Actually, $V$ cannot be more than $Y + 1$, so we must have $V = Y + 1$ because $c$ is just
  -- one more than $b$.
  have V_eq_Y_add_one : V = Y + 1 := by
    suffices V ≤ Y + 1 by linarith only [this, Y_lt_V]
    by_contra! h
    replace h : Y + 2 ≤ V := by linarith only [h]
    have := d_mem 2
    simp at this
    zify at b_eq c_eq h2 h this
    have :=
      calc (1:ℤ) = c - b := by rw [←h2]; ring
           _ = 5 * (V - Y) + (W - X) := by rw [b_eq, c_eq]; ring
           _ ≥ 10 + W - X := by linarith only [h]
           _ ≥ 10 - X := by linarith only
           _ ≥ 6 := by linarith only [this]
    contradiction

  -- and thus since $1$ and $2$ are the only digits left (we already know which letters are
  -- assigned to $0$, $3$, and $4$), we must have $V = 2$ and $Y = 1$.
  have V_eq_two : V = 2 := by
    have : V ∈ range 5 := d_mem 4 (by norm_num)
    simp at this
    interval_cases hV : V

    any_goals simp
    any_goals contradiction
    · have : Y = 0 := by linarith only [V_eq_Y_add_one]
      have : Y = W := by rw [this, W_eq_zero]
      simp [Y, W] at this
      have := h0 1 (by simp) 3 (by simp) this
      contradiction
    · have : V = Z := by rw [hV, Z_eq_three]
      simp [V, Z] at this
      have :=  h0 4 (by simp) 0 (by simp) this
      contradiction
    · have : V = X := by rw [hV, X_eq_four]
      simp [V, X] at this
      have :=  h0 4 (by simp) 2 (by simp) this
      contradiction

  have Y_eq_one : Y = 1 := by linarith only [V_eq_Y_add_one, V_eq_two]

  -- Thus $XYZ = 413_{5} = 4 \cdot 5^{2} + 1 \cdot 5 + 3 = 100 + 5 + 3 = 108$,
  -- which is answer $\boxed{\text{D}}$.
  simp [X, Y, Z] at X_eq_four Y_eq_one Z_eq_three
  simp [X_eq_four, Z_eq_three, Y_eq_one, ofDigits]