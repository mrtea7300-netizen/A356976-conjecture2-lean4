# Formal Lean 4 Proof of Zhi-Wei Sun's Conjecture 2 (OEIS A356976)

**Proof & Lean 4 formalization:** [@mrtea7300-netizen](https://github.com/mrtea7300-netizen)  
**Team contributors:** [@yotam1001](https://github.com/yotam1001), [@BoazCohenJ](https://github.com/BoazCohenJ), [@idangnlv](https://github.com/idangnlv), [@ohaventura](https://github.com/ohaventura), [@mrtea7300-netizen](https://github.com/mrtea7300-netizen)

A self-contained, zero-dependency, kernel-verified **Lean 4** proof of **Conjecture 2** from Zhi-Wei Sun's [OEIS A356976](https://oeis.org/A356976) (Nov. 16, 2021).

## Conjecture Statement (verbatim from OEIS A356976)

> **Conjecture 2:** For each positive integer $n$, the least positive integer $m$ such that those numbers $2k^3 + k$ ($k = 1..n$) are pairwise distinct modulo $m$, is just the least power of $2$ not smaller than $n$.

Previously verified computationally by Zhi-Wei Sun up to $n = 10^5$.

## Formal Theorem ([`A356976Conj2.lean`](A356976Conj2.lean))

```lean
def f (k : Nat) : Nat := 2 * k ^ 3 + k

def DistinctMod (n m : Nat) : Prop :=
  ∀ x y, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ n → f x % m = f y % m → x = y

theorem a356976_conjecture_2 (n : Nat) (hn : 1 ≤ n) :
    ∃ r : Nat,
      n ≤ 2 ^ r ∧
      (r = 0 ∨ 2 ^ (r - 1) < n) ∧
      DistinctMod n (2 ^ r) ∧
      ∀ m : Nat, 1 ≤ m → m < 2 ^ r → ¬ DistinctMod n m
```

## Verify Locally

Requires only **Lean 4** (tested on Lean `v4.36.0`) — **no Mathlib or external packages required**:

```bash
lean A356976Conj2.lean
```

Expected output (exit code `0`, zero warnings, zero `sorry`, zero `native_decide`):

```text
'A356976Conj2.a356976_conjecture_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

You can also run the standalone Python sanity check (reproduces OEIS A356976 for $n = 1..38$ and brute-force checks Conjecture 2 for $n = 1..300$):

```bash
python verify_conj2.py
```

## Proof Paper & Overview ([`paper.pdf`](paper.pdf) | [`paper.tex`](paper.tex) | [`proof.md`](proof.md))

1. **Upper bound ($m = 2^r$):** Since $f(y) - f(x) = (y - x)(2(x^2 + xy + y^2) + 1)$ and the second factor is always odd, $f$ is a bijection on $\mathbb{Z}/2^r\mathbb{Z}$.
2. **$3 \mid m$:** Since $3 \mid f(k)$ for all $k$, pigeonhole on $1 + j(m/3^e)$ ($0 \le j \le 3^{e-1}$) yields a collision $\le 1 + m/3 \le 2^{\lfloor \log_2 m \rfloor} + 1$.
3. **Any prime factor $p \ge 17$:** Setting $x = ud, y = vd$ reduces $m \mid (f(y) - f(x))$ to $u^2 + uv + v^2 \equiv -(2d^2)^{-1} \pmod{p^e}$ with $1 \le u < v \le (p^e - 1)/2$.
   - *Base case ($e = 1$):* Purely algebraic proof for all primes $p \ge 17$ via pigeonhole existence of one point on $X^2 + 3Y^2 \equiv 4c \pmod p$, stereographic parametrization (avoiding at most $14 < 17$ degenerate values of $t$), and a 2-case parity construction of $(u, v)$.
   - *Induction ($e \to e + 1$):* 5-line Pigeonhole Hensel Lifting step preserving $u, v \le (p^e - 1)/2$ with zero loss.
4. **Powers $5^3, 7^3, 11^2, 13^2 \mid m$:** Same Pigeonhole Hensel Lifting from in-kernel verified base witness tables.
5. **Remaining $m = 2^a \cdot s$ ($s \mid 5^2 \cdot 7^2 \cdot 11 \cdot 13$):** Direct witness tables for $a \ge 7$ (via $y = x + td$) and for all $245$ moduli with $0 \le a \le 6$, all verified by Lean's kernel `decide`.
