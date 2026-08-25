---
title: RiemannHIBS 当前状态
source: session
created: 2026-08-25
tags: [status]
schema_version: 2
audience: internal
last_confirmed: 2026-08-25
stage: current
---

# 当前状态 (2026-08-25)

## 已证 (无 sorry)
| 定理 | 位置 | 内容 |
|------|------|------|
| criticalLine_circle | Analytic.lean §6 | ‖exp(1/2+it)‖ = √e: 临界线像 = 圆周 |
| eta_eq_mul_zeta | Analytic.lean §4 | η = (1−2^{1−s})·ζ (Re s>1) |
| criticalPhaseC_envelope_circle | §7 | 相位截面经指数映射共圆 √e |
| expZeta_phase_principal | §8 | ζ̂(r·e^{iθ}) = ζ(log r + iθ) 主支 |
| phase_periodic / fold | §8 | 多圈叶 2πk 周期; 叶 π+2πk 折叠到负实轴 |
| envelope_universal_cover_branch | §8 | 每圈 k 有主支相位原像 |
| log_sqrt_exp_one | §11 | log(√e) = 1/2 (半径基本单位, 长度→对数) |
| critical_leaf_norm_locked | §11 | 临界叶上每项模长锁定 n^{-1/2} (长度维度锁定) |
| term_winding_number | §11 | 第 n 项缠绕圈数 = log(n+1) (windingCount, 角速度×叶数) |
| absolute_convergence_outside_critical_leaf | §11 | 绝对收敛分界 r>e (圆外更远叶绝对收敛) |
| critical_leaf_not_absolutely_convergent | §11 | 临界叶 (r=√e<e) 不绝对收敛 |
| zetaCoverIsomorphism | §12 | 覆盖↔复平面同构结构: covers(覆盖双射)+radial(径向单射)+zeta_eq(ζ 值一致)+branch(螺旋延续)+periodic(多叶折叠) — 全部由已证定理构成, 无 sorry |
| helix_continuation | §12 | 螺旋线延续: 每个 w≠0 的每圈 k 都有主支相位原像 (把"螺旋无限延伸"与"可数多叶"接起来) |
| mechanism_cycle_closed | §13 | 机制完备环 A⟹B⟹C⟹D⟹A 四方向全证 (A 圆外无零点⟹B 零点在圆上⟹C 包络半径锁定‖e^s‖=√e⟹D 经典 RH⟹A), 输入 h0: 0<Re s |
| infinitely_many_trivial_zeros | §15 | 零点集合为无限集: 单射嵌入 n↦−2(n+1), 每个是平凡零点 ζ(−2(n+1))=0 |

## 声明 (非证明)
- RiemannHypothesisHidden / C / Phase: RH 的隐数翻译
- riemannHypothesis_hidden_of_mathlib: 经典 RH ⟹ 隐数版 (单向)
- EnvelopeUniversalCoverMultiLog: 多值 log 分支 (draft)
- 非平凡零点无限多 (Hadamard 1893): 已证仅覆盖平凡零点 (§15); 非平凡部分需增长阶 + 因子分解/幅角原理; 已有机理皆"必要条件/缺增长"型, 不携带 ζ 的增长行为, 如实标注边界

## 诚实边界 (核心!)
- 机制链最后一步"圆外无零点" = RH 本身, 被当前提, 未证明
- zero_envelope_circle 的 hζ 参数未使用 → "零点定理"实为纯几何恒等式
- 螺旋无限延伸 ≠ 全称证明: 舞台(覆盖)完备 ≠ 演员(零点)在台上
- 机制完备环 (§13) 是"四方式等价"而非"零点真在圆上"的证明: 输入 h0 (`0 < Re s`, 零点在右半平面) 为显式机制假设 (经典事实但尚未在形式化层实现); D = `RiemannHypothesis` (mathlib 声明) 仍为被设对象 — 环的含义是"**若 RH 成立则四种说法一致**", 环本身不给 RH 真值。A⟹B 已证 (§9), 但 D⟹A 借 RH 声明, 闭环仍赖 RH 真值。

## 候选机制 (等价/直觉, 非力迫)
- 欧拉乘积正性 → Re s ≥ 1 无零点 (已证)
- Bohr–Landau/Selberg → 几乎所有零点在临界线附近 (密度)
- Möbius 平方根界: RH ⟺ M(x) = O(x^{1/2+ε}) (等价)
- 机制完备环 (§13): 圆外无零点⟺零点在圆上⟺包络半径锁定⟺RH (四方向等价 — 属等价规范而非真值证明)
- Berry–Keating xp 量子化 (speculative)
- 频率干涉: Z(t) ≈ 2Σ n^{-1/2}cos(θ−t·log n) (Riemann–Siegel, 数值验证)

## 图
全部 fig1–fig10 已登记于 `manifests/raw_sources.csv` (status=new)。

- fig1 `viz/fig1_projection_cross.png` 投影十字 (S/R/iR 三标签 → 复平面)
- fig2 `viz/fig2_envelope_shell.png` 三维包络壳
- fig3 `viz/fig3_critical_section.png` 临界截面
- fig4 `viz/fig4_phase_cover.png` 相位覆盖
- fig5 `viz/fig5_covering_space.png` + `viz/fig5_rollup.png` 覆盖空间 / 卷绕成圆周 |w|=√e (零点编号对应)
- fig6 `viz/fig6_winding.png` 绕数 (argument principle: 像曲线绕原点圈数 = 零点数)
- fig7 `viz/fig7_three_views.png` 三视图
- fig8 `viz/fig8_spiral_animation.gif` 螺旋动画 (万有覆盖螺旋柱面)
- fig9 `viz/fig9_mobius_walk.png` Möbius 行走
- fig10 `viz/fig10_zero_vibration.png` 频率干涉 Z(t)≈2Σn^{-1/2}cos(θ−t·log n) (Riemann–Siegel 数值)

数值验证图 (experiments/):
- `experiments/envelope_critical.png` 临界线圆周 |w|=√e 与零点共圆验证 (E1)
- `experiments/envelope_plane.png` 复平面/包络平面视图
- `experiments/envelope_surface.png` 包络曲面 w=log z (螺旋柱面/万有覆盖)
