import Mathlib.Tactic

-- A scout troop buys $1000$ candy bars at a price of five for $2$ dollars. They sell all the candy bars at the price of two for $1$ dollar.  What was their profit, in dollars?
-- $\textbf{(A) }\ 100      \qquad \textbf{(B) }\ 200      \qquad \textbf{(C) }\ 300      \qquad \textbf{(D) }\ 400      \qquad \textbf{(E) }\ 500$

theorem alg_1157
  (n : ℕ)
  (n_cand : n = 1000)
  (buy_price : ℚ)
  (sell_price : ℚ)
  (buy_price_eq : buy_price = 2 / 5)
  (sell_price_eq : sell_price = 1 / 2) :
    n * sell_price -  n * buy_price = 100 := by
  rw [n_cand, buy_price_eq, sell_price_eq]
  norm_num