(* ::Package:: *)

BeginPackage["ODEsTransformations`"];


(* ::Section:: *)
(*Usage *)


(* ::Subsection:: *)
(*Auxiliary Functions*)


	CollectCoefficients::usage = "
		CollectCoefficients[eq, y, x] receives an equation eq and returns a list with the coefficients of y''[x], y'[x] and y[x], respectivelly.
	";
	
	PrintSLEquation::usage = " 
		PrintSLEquation[p[x], q[x], y, x] returns (p[x] y'[x])' + q[x] y[x] = 0 in the Sturm-Liouville form.
	";
	
	PrintSLOperator::usage = " 
		PrintSLOperator[p[x], q[x], y, x, \[Lambda]] returns \[Lambda] y[x] = (p[x] y'[x])' + q[x] y[x] in the Sturm-Liouville form.
	";
	
	PrintLNEquation::usage = "
		PrintLNEquation[V, \[Lambda], y, x] returns y''[x]+(\[Lambda] +(V))y[x] == 0 holded as such.
	";

	ParenthesisWrapp::usage="
		ParenthesisWrapp[expr] wrapps expr with parenthesis of the, let's say, appropriate size. 
	";


(* ::Subsection:: *)
(*Main Functions*)


	TransformEQ::usage = "
		TransformEQ[eq, y, x, w[x], z] receives an equation eq w.r.t y[x] and returns the equation for z[x], where y[x]=w[x]z[x].
		TransformEQ[eq, y, x, w[x], z, t[x], s] receives an equation eq w.r.t y[x] and returns the equation for z[s], where y[x]=w[t[x]]z[t[x]] and t[x]==s.
	";

	SturmLiouvilleForm::usage = " 
	SturmLiouvilleForm[] prints a review of what is the Sturm-Liouville form.
	SturmLiouvilleForm[eq, y, x] gives the list {L y[x] == 0, \[Mu][x] p[x], \[Mu][x] r[x]} characterizing the Sturm-Liouville form of a second-order differential equation eq with function y[x].
	SturmLiouvilleForm[eq, y, x, \[Lambda]] gives the list {\[Lambda] y[x] == L y[x], \[Mu][x] p[x], \[Mu][x] r[x], - \[Mu][x] s[x]} characterizing the Sturm-Liouville form taking \[Lambda] as an eigenvalue.
	SturmLiouvilleForm[p[x], q[x], r[x], y, x] gives the list {L y[x] == 0, \[Mu][x] p[x], \[Mu][x] r[x]} characterizing the Sturm-Liouville form of p[x] y''[x] + q[x] y'[x] + r[x] y[x] == 0.
	SturmLiouvilleForm[p[x], q[x], r[x], y, x, \[Lambda]] gives the list {\[Lambda] y[x] == L y[x], \[Mu][x] p[x], \[Mu][x] r[x], - \[Mu][x] s[x]} characterizing the Sturm-Liouville form taking \[Lambda] as an eigenvalue.
	
	";	
	
	LiouvilleNormalForm::usage = " 
		LiouvilleNormalForm[] prints a review of what is the Liouville normal form.
		LiouvilleNormalFormFromEQ[eq, y, x, \[Lambda], \[Eta], \[Xi]] gives the list {\[Eta]''[\[Xi]] + (\[Lambda] + V[\[Xi]])\[Eta][\[Xi]] == 0, \[Eta]''[\[Xi]] + (\[Lambda] + V[\[Xi]])\[Eta][\[Xi]], V, \[Xi][x], \[CapitalPhi][x]}, the Liouville normal form data of eq = p[x] y''[x] + q[x] y'[x] + (r[x] + \[Lambda] s[x]) y[x].
		LiouvilleNormalForm[p[x], q[x], r[x], s[x], x, \[Lambda], \[Eta], \[Xi]] gives the list {\[Eta]''[\[Xi]] + (\[Lambda] + V[\[Xi]])\[Eta][\[Xi]] == 0, \[Eta]''[\[Xi]] + (\[Lambda] + V[\[Xi]])\[Eta][\[Xi]], V, \[Xi][x], \[CapitalPhi][x]} the Liouville normal form data of p[x] y''[x] + q[x] y'[x] + (r[x] + \[Lambda] s[x]) y[x] == 0.
	";



(* ::Section:: *)
(*Messages *)


	
	CollectCoefficients::areVarSet ="
		Vanishing coefficients. If the dependent and independent variables of your equation are not y and x, respectively, be sure to specify them. 
	";
	
	TransformEQ::invalidEQ = "
		Invalid equation. Recomended action: check arguments given. 	
	";
	
	LiouvilleNormalForm::invalidArgs1 = "
		Those are not valid functions. Please check usage, documentation or call LiouvilleNormalForm[] to review.
	";
	LiouvilleNormalForm::invalidArgs2 = "
		Those are not valid arguments. I'd check if they've been already assigned. If not, please check documentation.
	";


(* ::Section:: *)
(*Definitions*)


	Begin["`Private`"];



(* ::Subsection:: *)
(*Auxiliary Functions*)


		CollectCoefficients[eq_,y_:Global`y,x_:Global`x]:=( 
			Module[{ceq,coefFunc},
				ceq=Collect[eq,{y[x],y'[x],y''[x]}];
				coefFunc={Coefficient[ceq,y''[x]],Coefficient[ceq,y'[x]],Coefficient[ceq,y[x]]};
				If[coefFunc==={0,0,0},Message[CollectCoefficients::areVarSet]];
				Return[coefFunc]
			]
		)
		
		PrintSLEquationReview[p_:Global`p,q_:Global`q,y_:Global`y,x_:Global`x, d_:Global`d]:=( 
			
			Return@Defer@HoldForm[
						(HoldForm[d/(d x)](p[x] HoldForm[d/(d x)]) + q[x])y[x] == 0
			]
		)
		
		PrintSLEquation[]:=( 
			PrintSLEquationReview[]
		)
		
		PrintSLEquation[p_,q_,y_,x_, d_:Global`d]:=( 
			
			Return@Defer@HoldForm[
						(HoldForm[d/(d x)]HoldForm[(HoldForm[p] HoldForm[d/(d x)])] + q)y[x] == 0
			]
		)		
		
		PrintSLOperatorReview[p_:Global`p,q_:Global`q,m_:Global`\[Sigma],y_:Global`y,x_:Global`x,\[Lambda]_:Global`\[Lambda],d_:Global`d]:=( 
			Return@Defer@HoldForm[
						\[Lambda] y[x] == HoldForm[1/(m[x])] (HoldForm[HoldForm[d/(d x)](p[x] HoldForm[d/(d x)])]+q[x] )y[x]
			]
		)		
		PrintSLOperator[]:=( 
			PrintSLOperatorReview[]
		)
		PrintSLOperator[p_,q_,m_,y_,x_,\[Lambda]_,d_:Global`d]:=( 
			Return@Defer@HoldForm[
						\[Lambda] y[x] == HoldForm[1/(m)] (HoldForm[d/(d x)](HoldForm[p] HoldForm[d/(d x)])+q )y[x]
			]
		)
	
		ParenthesisWrapp/:MakeBoxes[ParenthesisWrapp[e__],form_]:=RowBox[{"(",MakeBoxes[Row[{e},","],form],")"}] (*I took this from: https://mathematica.stackexchange.com/questions/28962/matching-parentheses-size-in-plot-labels, thank you so much Carl Woll! *)
		
		PrintLNEquation[V_:Global`V,\[Lambda]_:Global`\[Lambda],y_:Global`y,x_:Global`x]:=(
			Return@HoldForm[ y''[x]+(\[Lambda] + V)y[x] == 0
			]
		)	
		
		PrintLNEquation[V_,\[Lambda]_,y_,x_]:=(
			Return@HoldForm[ y''[x]+(\[Lambda] + HoldForm[ParenthesisWrapp[V]])y[x] == 0
			]
		)	


(* ::Subsection:: *)
(*Main Functions*)


	
		TransformEQ[EQ_,Y_,X_,W_,z_:1,T_:0,Tname_:newcoord]:=(
			Module[{eq,w,x, g,aux1,aux2,aux3,aux4,coordtrans},
				If[Coefficient[EQ,Y[X]] === 0 && Coefficient[EQ,Y'[X]] === 0 && Coefficient[EQ,Y''[X]] === 0, 
					Message[TransformEQ::invalidEQ], 
					If[T =!= 0 && D[T,X] === 0, Message[TransformEQ::invalidTransf],
						eq=EQ/.X->x;
						w[x_]=W/.X->x;
						aux1=eq/.Y->Function[x, w[x]z[x]];
						aux2=aux1*(w[x])^(-1)//FullSimplify;
							If[T === 0,
								Return[Collect[aux2/.{x->X},{z[X],z'[X],z''[X]}]],
								coordtrans[x_]=T/.X->x;
								aux3=aux2/.z->Function[x,z[coordtrans[x]]]/.coordtrans[x]->Tname;
								aux4=aux3/Coefficient[aux3,z''[Tname]]//FullSimplify;
								Return[Collect[aux4/.{x->X},{z[Tname],z'[Tname],z''[Tname]}]]
							];
					];
				];
			];
		)
		
		
		SturmLiouvilleFormReview[p_:Global`p,q_:Global`q,r_:Global`r,s_:Global`s,y_:Global`y,x_:Global`x,\[Lambda]_:Global`\[Lambda],\[Mu]_:Global`\[Mu],L_:Global`L,\[Sigma]_:Global`\[Sigma],d_:Global`d]:=(
			CellPrint[{
				Cell["A second-order differential equation of the form:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[p[x] y''[x]+q[x] y'[x]+r[x]y[x]==0], "DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["is written in Sturm-Liouville form:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[(\[Mu][x]p[x] y'[x])'+\[Mu][x]r[x] y[x]==0],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["for:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[\[Mu][x]==HoldForm[1/p[x]] E^Integrate[q[x]/p[x],x]],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["If there is an eigenvalue of interest, say \[Lambda]:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[p[x] y''[x]+q[x] y'[x]+(r[x]+s[x] \[Lambda])y[x] == 0], "DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["Then the eigenvalue problem in Sturm-Liouville form reads:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[\[Lambda] y[x] == HoldForm[1/-(\[Mu][x]s[x])](HoldForm[d/(d x)](\[Mu][x]p[x] HoldForm[d/(d x)])+\[Mu][x]r[x]) y[x]],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["The Sturm-Liouville operator is given by:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[L = HoldForm[1/-(\[Mu][x]s[x])](HoldForm[d/(d x)](\[Mu][x]p[x] HoldForm[d/(d x)])+\[Mu][x]r[x])],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["And the measure associated to the eigenvalue \[Lambda] is:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[\[Sigma][x] = HoldForm[-(\[Mu][x]s[x])]],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["For self-adjoint Sturm-Liouville operators, the eigenfunctions are square-integrable w.r.t \[Sigma][x].","Text"]
				
			}];
		)	
		
		SturmLiouvilleForm[]:=( 
			SturmLiouvilleFormReview[];		
		)
		SturmLiouvilleForm[P_,Q_,R_,y_,x_,\[Lambda]_:0]:=( 
			Module[{\[Mu],p,q,m},
				
				\[Mu]=1/P E^Integrate[Q/P,x];
				p=FullSimplify[\[Mu] P];
				q=FullSimplify[\[Mu] R];
				
				If[\[Lambda]===0, 
					Return[{PrintSLEquation[p,q,y,x],p,q}]
				];

				If[\[Lambda]=!=0,
					If[NumericQ[\[Lambda]],
					Print["Please set a valid eigenvalue, this computation is symbolic."],
					m=(-Coefficient[Collect[q,\[Lambda]],\[Lambda]] )//FullSimplify;
						If[m===0,
						StringForm["`` is not an eigenvalue.",\[Lambda]],
						Return[{PrintSLOperator[p,Simplify[q + m*\[Lambda]],m,y,x,\[Lambda]],p,Simplify[q + m*\[Lambda]],m}]
						]
					]
				];
			];
		)
		
		SturmLiouvilleForm[eq_,y_,x_,\[Lambda]_:0]:=(
			Module[{coef},
			coef=CollectCoefficients[eq,y,x];
			SturmLiouvilleForm[coef[[1]],coef[[2]],coef[[3]],y,x,\[Lambda]]
			]
		)
		LiouvilleNormalFormReview[p_:Global`p,q_:Global`q,r_:Global`r,s_:Global`s,y_:Global`y,x_:Global`x,\[Lambda]_:Global`\[Lambda],V_:Global`V,\[Eta]_:Global`\[Eta],\[Xi]_:Global`\[Xi],\[CapitalPhi]_:Global`\[CapitalPhi]]:=(
			CellPrint[{
				Cell["A second-order equation:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[HoldForm[p[x]] HoldForm[y''[x]]+HoldForm[q[x]] HoldForm[y'[x]]+(HoldForm[r[x]]+HoldForm[s[x]] HoldForm[\[Lambda]])HoldForm[y[x]]==0], "DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["can be written in Liouville normal form:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[HoldForm[\[Eta]''[\[Xi]]]+(HoldForm[\[Lambda]]+HoldForm[V[\[Xi]]])HoldForm[\[Eta][\[Xi]]]==0],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["if the coefficient functions are sufficiently continuous and r is a strictly positive function. In the above expression, \[Lambda] is a parameter and V is usually called potential. The Liouville transformation of the dependent variable is given by:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[HoldForm[\[Eta][\[Xi]]]==HoldForm[\[CapitalPhi][x]]HoldForm[y[x]]],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["where the transformation of the independent variable is given by:","Text"],
				Cell[BoxData@ToBoxes[HoldForm[\[Xi][x]]==Integrate[Sqrt[HoldForm[(HoldForm[s[x]]/HoldForm[p[x]])]],x]],"DisplayFormula",CellMargins->{{300,0},{4,4}}],
				Cell["and such that:","Text"],
				Cell[BoxData@ToBoxes@HoldForm[\[CapitalPhi][x]==HoldForm[(HoldForm[s[x]]/HoldForm[p[x]])]^(1/4) E^(HoldForm[1/2]Integrate[HoldForm[q[x]/p[x]],x])],"DisplayFormula",CellMargins->{{300,0},{4,4}}]
			}]
		)	
		
		LiouvilleNormalForm[]:=( 
			LiouvilleNormalFormReview[];		
		)
		
		LiouvilleNormalForm[P_,Q_,R_,S_,x_,\[Lambda]_,\[Eta]_,\[Xi]name_]:=( 
			If[P===0||S===0,Message[LiouvilleNormalForm::invalidArgs1],
				Module[{p,q,r,t,eq,y,\[Xi],\[CapitalPhi],aux1,aux2,LNFormEQ,V},
					p[t_]=Q/P/.x->t;
					q[t_]=R/P/.x->t;
					r[t_]=S/P/.x->t;
					eq=P y''[ x]+Q y'[x]+(R+S \[Lambda])y[x]/.x->t;
					\[Xi]=\[Xi]name;
					\[Xi][t_]=Integrate[Sqrt[r[t]],t]//FullSimplify;
					\[CapitalPhi][t_]=r[t]^(1/4) E^(1/2 Integrate[p[t],t])//FullSimplify;
					aux1=eq/.y->Function[t,1/\[CapitalPhi][t] \[Eta][\[Xi][t]]]/.\[Xi][t]->\[Xi]//FullSimplify;
					aux2=Coefficient[aux1,\[Eta]''[\[Xi]]];
					If[aux2==0,Message[LiouvilleNormalForm::invalidArgs2]];
					LNFormEQ=aux1/aux2/.t->x//Simplify;
					V=Coefficient[aux1/aux2,\[Eta][\[Xi]]]-\[Lambda]/.t->x//Simplify;								
					Return[{PrintLNEquation[V, \[Lambda], \[Eta], \[Xi]],LNFormEQ, V, \[Xi][x], \[CapitalPhi][x]}];
				];
			];
		)
		
		LiouvilleNormalForm[eq_,y_,x_,\[Lambda]_,\[Eta]_,\[Xi]_]:=( 
			Module[{coef,aux1,aux2},
			coef=CollectCoefficients[eq,y,x];
			aux1=Coefficient[coef[[3]],\[Lambda]];
			aux2=coef[[3]]-\[Lambda] aux1; 
			LiouvilleNormalForm[coef[[1]],coef[[2]],aux2,aux1, x,\[Lambda],\[Eta],\[Xi]]
			]
		)		

	End[];
	
EndPackage[];

