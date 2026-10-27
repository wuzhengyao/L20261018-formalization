import L20261018.Hyp84
/-!
# `brOfH2` 的像在 `p`-挠内（R907）—— ζ-无关性 (b) 块的前提

`Br K` 只有 `ℕ`-纯量结构，故陈述用 `p • ·`。证明走 `calc` 逐段重写（避免 `rw` 链互抢匹配）：
`brOfH2 = h2MuToBr ∘ redEquiv`，两者都尊重 `ℕ`-纯量（`← map_nsmul`），而
`p • x = 0`（`GaloBase.H2 K p` 是 `ZMod p`-模，`(p : ZMod p) = 0`）。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}

/-- **`brOfH2` 的像在 `p`-挠内**（`ℕ`-纯量形式）。 -/
theorem p_smul_brOfH2 (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) :
    p • brOfH2 (p := p) (K := K) hζ x = 0 := by
  -- `H²(muNRep)` 也是 `ZMod p`-模 ⟹ `p • · = 0`（无需 `redEquiv` 的线性）
  have hpy : p • redEquiv (p := p) (K := K) hζ x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), CharP.cast_eq_zero (ZMod p) p, zero_smul]
  calc p • brOfH2 (p := p) (K := K) hζ x
      = p • ClassFieldTheory.h2MuToBr p K (redEquiv (p := p) (K := K) hζ x) := by
        rw [brOfH2_apply]
    _ = ClassFieldTheory.h2MuToBr p K (p • redEquiv (p := p) (K := K) hζ x) := by
        rw [← map_nsmul]
    _ = 0 := by rw [hpy, map_zero]

end H2Bridge

#print axioms H2Bridge.p_smul_brOfH2
