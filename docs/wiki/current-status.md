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
| zero_free_outside_envelope | §14 | 圆外远处无零点: Re(s)≥1 ⟹ ζ(s)≠0 (欧拉乘积每因子非零, mathlib riemannZeta_ne_zero_of_one_le_re) |
| zero_free_negative_side | §14 | 负侧无非平凡零点: Re(s)≤0 ⟹ ζ(s)≠0 (函数方程反射 + 14.1, 非负整数外) |
| nontrivial_zero_in_critical_strip | §14 | 非平凡零点 ⟹ 0<Re(s)<1 (临界带): 由 14.1+14.2 排除两侧 |
| nontrivial_zero_in_envelope_annulus | §14 | 非平凡零点 ⟹ 1<‖e^s‖<e (圆环内): ‖e^s‖=e^{Re s}, 临界叶√e 是圆环几何平均正中 |
| infinitely_many_trivial_zeros | §15 | 零点集合为无限集: 单射嵌入 n↦−2(n+1), 每个是平凡零点 ζ(−2(n+1))=0 |
| argumentPrinciple_single_zero | §16 | 隐数坐标系幅角原理原子: ∮dz/(z−w)=2πi (w 在圆内, mathlib circleIntegral) |
| envelope_circle_param | §16 | 圆 |z−c|=r 在相位包络坐标 = θ↦c+r·e^{iθ} (hEvalPhase 即圆参数化) |
| phase_winding_equals_zero_count | §16 | 相位缠绕 = 零点数×2πi (logDeriv 表述: 绕零点一圈相位变化 2π) |
| zeroCount_normalized | §16 | (2πi)⁻¹·∮dz/(z−w)=1 (幅角原理归一化: 除以 2πi 得零点数) |

## 声明 (非证明)
- RiemannHypothesisHidden / C / Phase: RH 的隐数翻译
- riemannHypothesis_hidden_of_mathlib: 经典 RH ⟹ 隐数版 (单向)
- EnvelopeUniversalCoverMultiLog: 多值 log 分支 (draft)
- 非平凡零点无限多 (Hadamard 1893): 已证仅覆盖平凡零点 (§15); 非平凡部分需增长阶 + 因子分解/幅角原理; 已有机理皆"必要条件/缺增长"型, 不携带 ζ 的增长行为, 如实标注边界

## 诚实边界 (核心!)
- 圆外远处无零点已证 (Re≥1, §14 欧拉乘积); 但 1/2<Re<1 的圆外部分 (=RH 核心未解区) 仍未被覆盖 — 机制链"圆外无零点"现在分两段: 远处已证, 临界带内仍是 RH
- 机制完备环 (§13) 是"四方式等价"而非"零点真在圆上"的证明: 输入 h0 (`0 < Re s`, 零点在右半平面) 为显式机制假设 (经典事实但尚未在形式化层实现); D = `RiemannHypothesis` (mathlib 声明) 仍为被设对象 — 环的含义是"**若 RH 成立则四种说法一致**", 环本身不给 RH 真值。A⟹B 已证 (§9), 但 D⟹A 借 RH 声明, 闭环仍赖 RH 真值。
- 幅角原理 (§16) 已构造为隐数坐标系内的机制原子 (相位缠绕=零点数), 但它是"电路"缺"电源": 无限零点的输出依赖 ζ 在围道边界的增长估计 (N(T)~T/2π·log(T/2π)) — 该输入是 ζ 的分析性质, 坐标变换翻译不掉, 非平凡零点无限多仍标注为边界
- 螺旋无限延伸 ≠ 全称证明: 舞台(覆盖)完备 ≠ 演员(零点)在台上
- 非平凡零点存在性与无限性: 已证仅平凡零点无限 (§15); 非平凡部分需增长阶+因子分解/幅角原理, 已有机理皆"必要条件/缺增长"型, 不携带 ζ 的增长行为, 如实标注边界

## 候选机制 (等价/直觉, 非力迫)
- 欧拉乘积正性 → Re s ≥ 1 无零点: 已在 §14 形式化 (zero_free_outside_envelope, mathlib riemannZeta_ne_zero_of_one_le_re)
- Bohr–Landau/Selberg → 几乎所有零点在临界线附近 (密度)
- Möbius 平方根界: RH ⟺ M(x) = O(x^{1/2+ε}) (等价)
- 机制完备环 (§13): 圆外无零点⟺零点在圆上⟺包络半径锁定⟺RH (四方向等价 — 属等价规范而非真值证明)
- 隐数坐标系幅角原理 (§16): 相位缠绕=零点数 已证为机制原子; 完整无限零点需增长估计输入
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
