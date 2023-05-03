declare
Car
Cdr
Node
Preorder
LexAux
Lex
Infix2Prefix
Expression
EncWithPrefix
FeedFile
ReadFile
IsPrimitive
ParseAlgebra
ParseSuperComb
ParseCall
FindNext
EvalPrimitive
Eval
Test

fun {Car L}
    case L 
    of nil then nil
    [] H | _ then H
    end
end

fun {Cdr L}
    case L
    of nil then nil
    [] _ | R then R
    end
end

class Node
    attr val left right
    
    meth init(Value)
        val := Value
        left := nil
        right := nil
    end

    meth setLeft(Left)
        left := Left
    end

    meth setRight(Right)
        right := Right
    end

    meth val($)
        @val
    end

    meth isEval($)
        {Number.is @val}
    end

    meth setVal(Value)
        val := Value
    end

    meth left($)
        @left
    end

    meth right($)
        @right
    end

    meth transplant(R)
        {self setVal({R val($)})}
        {self setLeft({R left($)})}
        {self setRight({R right($)})}
    end
end

proc {Preorder Node}
    local
        fun {Aux Node Acc}
            if Node \= nil then
                local Step1 Step2 in
                    Step1 = {Node val($)} | Acc
                    Step2 = {Aux {Node left($)} Step1}
                    {Aux {Node right($)} Step2}
                end
            else
                Acc
            end
        end
    in
        {Browse {List.reverse {Aux Node nil}}}
    end
end

fun {LexAux Stream Tokens Carry}
    local
        Keywords = ["fun" "var" "in" "+" "-" "*" "/" "=" "(" ")"]

        fun {CaptureSymbol}
            if Carry \= nil then {Reverse Carry} | Tokens
            else Tokens
            end
        end

        fun {CaptureKeyword}
            local Match = fun {$ Keyword} {List.isPrefix Keyword Stream} end in
                {Car {List.filter Keywords Match}}
            end
        end
    in
        if Stream \= nil then 
            local Keyword = {CaptureKeyword} in
                if Keyword \= nil then
                    local Forward = {List.drop Stream {List.length Keyword}} in
                        {LexAux Forward (Keyword | {CaptureSymbol}) nil}
                    end
                else
                    local H | R = Stream in
                        if {Char.isSpace H} then
                            {LexAux R {CaptureSymbol} nil}
                        else
                            {LexAux R Tokens (H | Carry)}
                        end
                    end
                end
            end
        else
            {CaptureSymbol}
        end
    end
end

fun {Lex Stream}
    {List.reverse {LexAux Stream nil nil}}
end

fun {Infix2Prefix Data}
    local Reverse Infix2Postfix in
        fun {Reverse Data Ans}
            case Data of H|T then
                case H of "(" then
                    {Reverse T ")"|Ans}
                []  ")" then
                    {Reverse T "("|Ans}
                else
                    {Reverse T H|Ans}
                end
            else
                Ans
            end
        end
        fun {Infix2Postfix Data Stack Res}
            local PopWhile in
                fun {PopWhile Stack Res Cond}
                    case Stack of H|T then
                        if {Cond H} then
                            {PopWhile T H|Res Cond}
                        else
                            [Res Stack]
                        end
                    else
                        [Res Stack]
                    end
                end
                case Data of H|T then
                    case H of "(" then
                        {Infix2Postfix T H|Stack Res}
                    [] ")" then
                        local H2 T2 T3 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {Not X=="("} end}
                            _|T3 = T2
                            {Infix2Postfix T T3 H2}
                        end 
                    [] "+" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X ["*" "/"]} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "-" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X ["*" "/"]} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "*" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X nil} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "/" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X nil} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    else
                        {Infix2Postfix T Stack H|Res}
                    end
                else 
                    Res
                end
            end
        end
        {Infix2Postfix "("|{Reverse "("|Data nil} nil nil}
    end
end

class Expression
    attr body bindings

    meth init
        body := nil
        bindings := {New Store init}
    end

    meth nbinds($)
        {@bindings size($)}
    end

    meth bindings($)
        @bindings
    end

    meth ids($)
        {@bindings names($)}
    end

    meth body($)
        @body
    end

    meth setBody(Body)
        body := Body
    end

    meth addBinding(Id)
        {@bindings add(Id {New Node init(Id)})}
    end

    meth bind(Id Expr)
        local B = {@bindings find(Id $)} in
            {B transplant(Expr)}
        end
    end
end

fun {EncWithPrefix Prefix Str}
    {String.toAtom {List.append Prefix Str}}
end

class Store
    attr values

    meth init
        values := {Dictionary.new}
    end

    meth add(Name Value)
        local Encoded = {EncWithPrefix "store" Name} in
            {Dictionary.put @values Encoded Value}
        end
    end

    meth find(Name $)
        local Encoded = {EncWithPrefix "store" Name} in
            {Dictionary.condGet @values Encoded nil}
        end
    end

    meth size($)
        {List.length {Dictionary.keys @values}}
    end

    meth names($)
        {Dictionary.keys @values}
    end
end

fun {FeedFile Path}
    local
        Stream
        Tokens
        Processed
    in
        {ReadFile Path Stream}
        Tokens = {Lex Stream}
        {Infix2Prefix Tokens}
    end
end

proc {ReadFile Path ?Result}
    local F in
        F = {New Open.file init(name:Path flags:[read])}
        {F read(list:Result size:all)}
        {F close}
    end
end

fun {IsPrimitive C}
    {List.member C ["+" "-" "*" "/"]}
end

proc {ParseAlgebra Tokens Expr ?Remaining}
    local
        proc {Scaffold Op Arg1 Arg2 ?NodeOut}
            local
                Temp = {New Node init(app)}
                OpNode = {New Node init(Op)}
            in
                NodeOut = {New Node init(app)}
                {NodeOut setRight(Arg2)}

                {Temp setLeft(OpNode)}
                {Temp setRight(Arg1)}

                {NodeOut setLeft(Temp)}
            end
        end

        proc {Aux Tokens ?NodeOut ?Remaining}
            case Tokens
            of nil then Remaining = nil
            [] Head | Rest then
                if {IsPrimitive Head} then
                    local Arg1 Arg2 Break in
                        {Aux Rest Arg1 Break}
                        {Aux Break Arg2 Remaining}
                        {Scaffold Head Arg1 Arg2 NodeOut}
                    end
                else
                    if {List.all Head Char.isDigit} then
                        NodeOut = {New Node init({String.toInt Head})}
                    else
                        local B = {{Expr bindings($)} find(Head $)} in 
                            if B \= nil then
                                NodeOut = B
                            else
                                NodeOut = {New Node init(Head)}
                                {{Expr bindings($)} add(Head NodeOut)}
                            end
                        end
                    end
                    Remaining = Rest
                end
            end
        end
    in
        local Body in
            {Aux Tokens Body Remaining}
            {Expr setBody(Body)}
        end
    end
end

proc {ParseSuperComb Env Tokens ?Remaining}
    local
        F = {New Expression init}

        proc {ParseArgs Tokens ?Remaining}
            local Args in
                {List.takeDropWhile Args Remaining fun {$ X} X \= "=" end}

                for A in Args do
                    {F addBinding(A)}
                end
            end
        end

        proc {ParseBody Tokens ?Remaining}
            {ParseAlgebra Tokens F Remaining}
        end

        proc {Aux Tokens ?Remaining}
            case Tokens
            of nil then Remaining = nil
            [] Name | R then
                local Break in
                    {ParseArgs R Break}
                    {ParseBody {Cdr Break} Remaining}
                    {Env add(Name F)}
                end
            end
        end
    in
        {Aux Tokens Remaining}
    end
end

proc {Copy ExprIn ?ExprOut}
    local
        proc {Aux TreeIn Bindings ?TreeOut}
            if TreeIn \= nil then
                local
                    V = {TreeIn val($)}
                    Left
                    Right
                in
                    if {Or {Number.is V} (V == app)} then
                        TreeOut = {New Node init(V)}
                    else
                        local B = {Bindings find(V $)} in
                            if B \= nil then
                                TreeOut = B
                            else
                                TreeOut = {New Node init(V)}
                                {Bindings add(V TreeOut)}
                            end
                        end
                    end
                    {Aux {TreeIn left($)} Bindings Left}
                    {Aux {TreeIn right($)} Bindings Right}
                    {TreeOut setLeft(Left)}
                    {TreeOut setRight(Right)}
                end
            else
                TreeOut = nil
            end
        end
        Body
    in
        ExprOut = {New Expression init}
        {Aux {ExprIn body($)} {ExprOut bindings($)} Body}
        {ExprOut setBody(Body)}
    end
end

fun {ParseCall Tokens}
    local
        fun {Aux Tokens TreePrev}
            case Tokens
            of nil then TreePrev
            [] H | R then
                local Chain = {New Node init(app)} in
                    {Chain setLeft(TreePrev)}
                    {Chain setRight({New Node init(H)})}
                    {Aux R Chain}
                end
            end
        end
    in
        {Aux {Cdr Tokens} {New Node init({Car Tokens})}}
    end
end

fun {FindNext Expr}
    local
        fun {Aux Current Acc}
            if Current \= nil then
                {Aux {Current left($)} (Current | Acc)}
            else
                Acc
            end
        end
    in
        {Aux Expr nil}
    end
end

proc {ZipArgs Root F}
    local
        C = {Copy F}

        proc {Aux Current Args} 
            case Args
            of nil then skip
            [] H | R then
                {C bind(H {Current right($)})}
                {Aux {Current left($)} R}
            end
        end
    in
        {Aux Root {F ids($)}}
        {Root transplant({C body($)})}
    end
end

proc {ReplaceSuperComb Env Name Stack}
    local
        F = {Env find(Name $)}
        Root = {Car {List.drop Stack {F nargs($)}}}
    in
        {ZipArgs Root F}
    end
end

proc {EvalPrimitive Env Primitive Stack}
    local
        Op = case Primitive
            of "+" then fun {$ X Y} X + Y end
            [] "-" then fun {$ X Y} X - Y end
            [] "*" then fun {$ X Y} X * Y end
            [] "/" then fun {$ X Y} X / Y end
        end

        Root = {Car {List.drop Stack 2}}

        Arg1 = {{Root left($)} right($)}
        Arg2 = {Root right($)}
        Result
    in
        if {Not {Arg1 isEval($)}} then
            {Eval Env Arg1}
        end

        if {Not {Arg2 isEval($)}} then
            {Eval Env Arg2}
        end

        Result = {Op {Arg1 val($)} {Arg2 val($)}}
        {Root setVal(Result)}
        {Root setLeft(nil)}
        {Root setRight(nil)}
    end
end

proc {Eval Env Expr}
    local
        Stack = {FindNext Expr}
        Name = {{Car Stack} val($)}
    in
        if {IsPrimitive Name} then
            {EvalPrimitive Env Name Stack}
        else
            {ReplaceSuperComb Env Name Stack}
            {Eval Env Expr}
        end
    end
end

proc {Test}
    local
        Tokens = {FeedFile "./testcases/simple.txt"}
        Env = {New Store init}
        Expr
        Remaining
    in
        {ParseAlgebra Tokens Expr Remaining}
        {Eval Env Expr}
        {Preorder Expr}
    end
end

{Test}