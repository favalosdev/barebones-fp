declare
Car
Cdr
Node
Preorder
LexAux
Lex
Infix2Prefix
Function
EncWithPrefix
FeedFile
ReadFile
IsOperator
ParseAlgebra
% ParseSuperComb
% ParseCall
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

class Function
    attr name args body

    meth init
        name := nil
        args := nil
        body := nil
    end

    meth name($)
        @name
    end

    meth nargs($)
        {List.length @args}
    end

    meth args($)
        @args
    end

    meth body($)
        @body
    end

    meth setName(Name)
        name := Name
    end

    meth addArg(Arg)
        args := Arg | @args
    end

    meth setBody(Body)
        body := Body
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

fun {IsOperator C}
    {List.member C ["+" "-" "*" "/"]}
end

proc {ParseAlgebra Tokens ?Expr ?Remaining}
    local
        ArgNodes = {New Store init}

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
                if {IsOperator Head} then
                    local Arg1 Arg2 Break in
                        {Aux Rest Arg1 Break}
                        {Aux Break Arg2 Remaining}
                        {Scaffold Head Arg1 Arg2 NodeOut}
                    end
                else
                    if {List.all Head Char.isDigit} then
                        NodeOut = {New Node init({String.toInt Head})}
                    else
                        local Arg = {ArgNodes find(Head $)} in
                            if Arg \= nil then
                                NodeOut = Arg
                            else
                                NodeOut = {New Node init(Head)}
                                {ArgNodes add(Head NodeOut)}
                            end
                        end
                    end
                    Remaining = Rest
                end
            end
        end
    in
        {Aux Tokens Expr Remaining}
    end
end

/*
proc {ParseSuperComb Tokens ?Remaining}
    local
        F = {New Function init}

        proc {ParseArgs Tokens ?Remaining}
            local Args in
                {List.takeDropWhile Args Remaining}

                if Args \= nil then
                    for Arg in {String.tokens Args & } do
                        {F addArg(Arg)}
                    end
                end
            end
        end

        proc {ParseBody Tokens ?Remaining}
            local Root in
                {ParseAlgebraicExpr Tokens Root Remaining}
                {F setBody(Root)}
            end
        end

        proc {Aux Tokens ?Remaining}
            case Tokens
            of nil then nil
            [] Name | R then
                local Break in
                    {F setName(H)}
                    {ParseArgs R Break}
                    {ParseBody Break Remaining}
                end
            end
        end
    in
        {Aux Tokens Remaining}
        {Env add(F)}
    end
end
*/

% A tree is built in curried fashion
/*
proc {ParseCall Tokens}
    local
        proc {Aux Tokens}
            local H | R = Tokens in
                if R \= nil then app(H {Aux R})
                else H end
            end
        end
    in
        {Aux Tokens}
    end
end
*/

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

/*
fun {EvalSuperComb}
end
*/

proc {EvalPrimitive Primitive Stack}
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
    in
        if {Not {Arg1 isEval($)}} then
            {Eval Arg1}
        end

        if {Not {Arg2 isEval($)}} then
            {Eval Arg2}
        end

        {Root setVal({Op {Arg1 val($)} {Arg2 val($)}})}
        {Root setLeft(nil)}
        {Root setRight(nil)}
    end
end

proc {Eval Expr}
    local
        Stack = {FindNext Expr}
        Outermost = {Car Stack}
        Name = {Outermost val($)}
    in
        % If primitive, evaluate
        if {IsOperator Name} then
            {EvalPrimitive Name Stack}
        end
    end
end

proc {Test}
    local
        Tokens = {FeedFile "./testcases/simple.txt"}
        Expr
        Remaining
    in
        {ParseAlgebra Tokens Expr Remaining}
        {Eval Expr}
        {Preorder Expr}
    end
end

{Test}