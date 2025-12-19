# HastTable Strategies说明文档
（实际上是尝试写strategies的学习笔记）

# 作用与术语

- left / right 表示|--两侧资源； *_erase(k) 消耗匹配到的第 k 个资源， *_add(...) 在对应侧新增资源或纯等式。
- *_exist_add(x) 在当前侧引入存在变量以继续化简。
- priority 控制搜索顺序； unfold_* / fold_* 表示结构的展开与折叠。
- action代表化简操作

# 规则清单
- id 0: 空单链表左侧基例，推出指针为空
- id 1: 空单链表右侧基例，推出指针为空
- id 2: 右侧 sll(NULL, l) ，推出l为空链表
- id 3: 两侧非空 sll 列表头部统一，生成 x0==x1 、 l0==l1
- id 4: 左侧 sll(p, l0) ，右侧 sll(p, l1) ，推出 l0==l1
- id 5: 左侧 sll 在指针非空的情况下展开到 cons 形，并引入节点字段
- id 6: 右侧 sll 在指针非空的情况下展开到 cons 形，并引入节点字段
- id 7: 左侧非空 sll 展开为 next 指针和尾段
- id 8: 右侧非空 sll 展开（要求 p!=0 ），引入 next 与尾段；
- id 9/10/11/12/27: 本质上都是sllseg(p, p, l) + sll(p, l0)推出l为空
- id 13: 两侧对齐同一 q 指针数据时列表统一
- id 14: sllbseg 与未定义数据两侧统一，同时统一中间指针 q==r
- id 15: 左侧指针为 NULL 时右侧 sll(p,l) 化为空列表；
- id 16: 左侧非空 sll 展开为 next 字段和尾段，并令 l==cons{Z}(d,l0)
- id 17: 有 val 与 next 字段和尾段时折叠成 sll(p,l) ，并令 l==cons{Z}(d,l0)
- id 18: dllseg 左右统一（两段同形）生成 l0==l1 ；
- id 19: 右侧空双链表基例： dll(NULL, up, l) 化为空列表；
- id 20: 左侧非空双链表展开：引入 down/up 字段、前驱子段，并令 l==cons{Z}(p,l0)
- id 21: 双链表折叠：有 down/up 字段与子段 dll(down,p,l0) 时折叠为 dll(p, up, l) 并统一 l==cons{Z}(p,l0)
- id 22: 右侧 dllseg(?x, x, x_up, y_up, l) 基例：端点相同则 x_up==y_up 且列表为空
- id 23: 左侧非空 dllseg 展开：引入 down 与 up 字段、递归子段，列表前缀为当前结点；
- id 24: dllseg 左右统一（两段同形）生成 l0==l1
- id 25: 右侧 sllseg(?p,0,l) 桥接成 sll(p,l)
- id 26: 右侧 dllseg(?p,0,up,y_up,l) 桥接成 dll(p,up,l)