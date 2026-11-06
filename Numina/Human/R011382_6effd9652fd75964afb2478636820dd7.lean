import Mathlib

/- 5. To transmit a three-letter word through a channel, the following method is used. Each letter of the word is assigned a pair of digits according to the rule: А -00, Б $-01, \mathrm{~B}-02, \ldots$, Я - 32. After that, the obtained sequence of digits $m_{1}, m_{2}, \ldots, m_{6}$. is transformed by the formula:

$c_{i}=f\left(m_{i}, c_{\{i-1\}}\right), i \in\{1, \ldots, 6\}$.

where $c_{0} \in\{0, \ldots, 9\}$ - a randomly chosen digit and $f(x, y)=r_{10}(x+4 y)-$ the remainder of the division by 10 of the number $x+4 y$. Then the sequence $c_{0}, c_{1}, \ldots, c_{6}$ is transmitted through the channel. Crypto managed to intercept $\left(c_{0}, c_{2}, c_{4}, c_{6}\right)=(1,3,7,1)$, what word could have been transmitted through the channel? Provide the word in your answer (in lowercase letters). -/
theorem algebra_240215 (c : Fin 7 → ℕ) (m : Fin 6 → ℕ) (hc : ∀ i, c (i + 1) = (m i + 4 * c i) % 10)
  (h : c 0 = 1 ∧ c 2 = 3 ∧ c 4 = 7 ∧ c 6 = 1) :
  m = ![1, 3, 0, 9, 2, 1] → c = ![1, 5, 3, 2, 7, 0, 1] := by intro hm; ext i; match i with
  -- simply unfold all the definitions using the relation and conclude
  -- the word is миф, meaning 'myth'
  | 0 => rw [h.1]; rfl
  | 1 => rw [show c 1 = c (0 + 1) by rfl, hc 0, h.1, hm]; rfl
  | 2 => rw [show c 2 = c (1 + 1) by rfl, hc 1, show c 1 = c (0 + 1) by rfl, hc 0, h.1, hm]; rfl
  | 3 => rw [show c 3 = c (2 + 1) by rfl, hc 2, h.2.1, hm]; rfl
  | 4 => rw [show c 4 = c (3 + 1) by rfl, hc 3, show c 3 = c (2 + 1) by rfl, hc 2, h.2.1, hm]; rfl
  | 5 => rw [show c 5 = c (4 + 1) by rfl, hc 4, h.2.2.1, hm]; rfl
  | 6 => rw [show c 6 = c (5 + 1) by rfl, hc 5, show c 5 = c (4 + 1) by rfl, hc 4, h.2.2.1, hm]; rfl