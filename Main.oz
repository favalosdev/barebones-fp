declare

% Utilities
Car
Cdr
EncWithPrefix
Store
ReadFile
IsPrimitive
IsANumber
BuildTree

% String processing
LexAux
Lex
Infix2Prefix

% Node
Node
Preorder

% Template
Template

% Parsing
ParseBody
ParseSuperComb
ParseCall
ParseProgram

% Expression reduction
FindNext
Instantiate
ReplaceSuperComb
EvalPrimitive
Eval

Test

% Utilities

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

fun {EncWithPrefix Prefix Str}
    {String.toAtom {List.append Prefix {List.append "_" Str}}}
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

    meth has(Name $)
        local Encoded = {EncWithPrefix "store" Name} in
            {Dictionary.member @values Encoded}
        end
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

fun {IsANumber Str}
    local
        AllDigits = fun {$ Y} {List.all Y Char.isDigit} end
        IntPart
        DecPart
    in
        {List.takeDropWhile Str fun {$ X} X \= &. end IntPart DecPart}
        {And {AllDigits IntPart} {AllDigits DecPart}}
    end
end

proc {BuildTree Env Joiner Lifter Tokens ?TreeOut}
    local
        fun {Join Trees}
            {List.foldL Trees Joiner nil}
        end

        proc {Aux Tokens TreePrev ?TreeOut ?Remaining}
            case Tokens
            of nil then Remaining = nil
            [] H | R then
                if {Or {IsPrimitive H} {Env has(H $)}} then
                    local
                        Break = {NewCell R}
                        Trees = {NewCell [{Lifter H}]}
                        N = if {IsPrimitive H} then 2 else {List.length {{Env find(H $)} args($)}} end
                    in
                        for I in 1..N do
                            local Tr B in
                                {Aux @Break nil Tr B}
                                Trees := Tr | @Trees
                                Break := B
                            end
                        end
                        TreeOut = {Join (TreePrev | {List.reverse @Trees})}
                        Remaining = @Break
                    end
                else
                    local ToLift = if {IsANumber H} then {String.toFloat H} else H end in
                        TreeOut = {Joiner TreePrev {Lifter ToLift}}
                    end
                    Remaining = R
                end
            end
        end

        Dummy
    in
        {Aux {Infix2Prefix Tokens} nil TreeOut Dummy}
    end
end

%------------

% String processing

fun {LexAux Stream Tokens Carry}
    local
        Keywords = ["let" "in" "+" "-" "*" "/" "=" "(" ")"]

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

%------------

% Node related definitions

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

    meth replace(R)
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

%-------------

% Template related definitions

class Template
    attr args bindings body

    meth init
        args := nil
        bindings := {Dictionary.new}
        body := nil
    end

    meth args($)
        @args
    end

    meth setArgs(Args)
        args := Args
    end

    meth hasArg(Name $)
        {List.member Name @args}
    end

    meth addBinding(Id Body)
        local Encoded = {EncWithPrefix "binding" Id} in
            {Dictionary.put @bindings Encoded Body}
        end
    end

    meth hasBinding(Id $)
        local Encoded = {EncWithPrefix "binding" Id} in
            {Dictionary.member @bindings Encoded}
        end
    end

    meth getBinding(Id $)
        local Encoded = {EncWithPrefix "binding" Id} in
            {Dictionary.get @bindings Encoded}
        end
    end

    meth body($)
        @body
    end

    meth setBody(Body)
        body := Body
    end
end

%-------------

% Expression evaluation 

% Finds the next primitive or supercombinator to reduce
fun {FindNext Expr}
    local
        fun {Aux Current Acc}
            if Current == nil then Acc
            else {Aux {Current left($)} (Current | Acc)}
            end
        end
    in
        {Aux Expr nil}
    end
end

/*
Takes a template, makes a copy, binds the arguments according to
expression graph and return the modified graph with the instantia-
ted template.
*/
proc {Instantiate Temp Root}
    local
        ArgBindings = {New Store init}
        IntBindings = {New Store init}

        proc {Aux NodeIn ?NodeOut}
            case NodeIn
            of nil then NodeOut = nil
            [] app(L R) then
                local Left Right in
                    {Aux L Left}
                    {Aux R Right}
                    NodeOut = {New Node init(app)}
                    {NodeOut setLeft(Left)}
                    {NodeOut setRight(Right)}
                end
            [] Value then
                if {Or {Number.is Value} {IsPrimitive Value}} then
                    NodeOut = {New Node init(Value)}
                elseif {Temp hasBinding(Value $)} then
                    if {IntBindings has(Value $)} then
                        NodeOut = {IntBindings find(Value $)}
                    else
                        NodeOut = {Aux {Temp getBinding(Value $)}}
                        {IntBindings add(Value NodeOut)}
                    end
                elseif {Temp hasArg(Value $)} then
                    if {ArgBindings has(Value $)} then
                        NodeOut = {ArgBindings find(Value $)}
                    else
                        NodeOut = {New Node init(Value)}
                        {ArgBindings add(Value NodeOut)}
                    end
                else
                    /*
                    This guard has to be left in order to account
                    for literals that are not binded
                    */
                    NodeOut = {New Node init(Value)}
                end
            end
        end

        proc {ZipArgs Current Args}
            case Args
            of nil then skip
            [] H | R then
                local
                    AB = {ArgBindings find(H $)}
                    ToZip = {Current right($)}
                    Next = {Current left($)}
                in
                    {AB replace(ToZip)}
                    {ZipArgs Next R}
                end
            end
        end

        Instance = {Aux {Temp body($)}}
    in
        {ZipArgs Root {List.reverse {Temp args($)}}}
        {Root replace(Instance)}
    end
end

% Finds an existing supercombinator and instantiates it
proc {ReplaceSuperComb Env Stack Name}
    local
        Temp = {Env find(Name $)}
        Root = {Car {List.drop Stack {List.length {Temp args($)}}}}
    in
        {Instantiate Temp Root}
    end
end

/*
Evaluates a primitive by first checking if its
arguments are evaluated and then carrying out
the operation itself
*/
proc {EvalPrimitive Env Stack Primitive}
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
        % Try to evaluate the arguments

        if {Not {Arg1 isEval($)}} then
            {Eval Env Arg1}
        end

        if {Not {Arg2 isEval($)}} then
            {Eval Env Arg2}
        end

        % Check if the arguments "collapsed" into a value

        local
            V1 = {Arg1 val($)}
            V2 = {Arg2 val($)}
        in
            if {And {Number.is V1} {Number.is V2}} then
                {Root setVal({Op V1 V2})}
                {Root setLeft(nil)}
                {Root setRight(nil)}
            elseif {Number.is V1} then
                {Root setLeft(V1)}
            elseif {Number.is V2} then
                {Root setRight(V2)}
            end
        end
    end
end

/*
Evaluates an expression graph by doing the following:
(1) Finding the next supercombinator or primitive to reduce
(2) If it is a primitive, execute the method EvalPrimitive
(3) If it is a supercombinator, replace its instantiated
    template i.e. template with binded args in the expression
    graph. Then call Eval once again.

This method is performed until there is nothing more to reduce.
 */
proc {Eval Env Expr}
    local
        Stack = {FindNext Expr}
        Next = {{Car Stack} val($)}
        IsSuperComb = fun {$ Name} {Env has(Name $)} end
    in
        if {IsPrimitive Next} then
            {EvalPrimitive Env Stack Next}
        elseif {IsSuperComb Next} then
            {ReplaceSuperComb Env Stack Next}
            {Eval Env Expr}
        end
    end
end

%-----------

% Parsing: all this functions are pretty self-explanatory

proc {ParseBody Env Tokens ?Result}
    local
        fun {Joiner Prev Curr}
            if Prev \= nil then
                app(Prev Curr)
            else
                Curr
            end
        end

        fun {Lifter Value}
            Value
        end
    in
        {BuildTree Env Joiner Lifter Tokens Result}
    end
end

proc {ParseBinding Env Temp Tokens}
    local
        "let" | Name | R = Tokens
        Algebra = {ParseBody Env R}
    in
        {Temp addBinding(Name Algebra)}
    end
end

proc {ParseSuperComb Env Line}
    local
        Temp = {New Template init}
        Parts = {String.tokens Line &=}

        Sig = {Lex {List.nth Parts 1}}
        Name | Args = Sig
        
        Def = {Lex {List.foldL {Cdr Parts} List.append nil}}
    in
        {Temp setArgs(Args)}

        % This is an ugly hack but hey, it gets the job done
        local Algebra in 
            if {List.member "in" Def} then
                local Binding Rest in
                    {List.takeDropWhile Def fun {$ X} X \= "in" end Binding Rest}
                    {ParseBinding Env Temp Binding}
                    Algebra = {Cdr Rest}
                end
            else
                Algebra = Def
            end

            {Temp setBody({ParseBody Env Algebra})}
        end

        {Env add(Name Temp)}
    end
end

proc {ParseCall Env Line ?Expr}
    local
        proc {Joiner Prev Curr ?Joined}
            if Prev \= nil then
                Joined = {New Node init(app)}
                {Joined setLeft(Prev)}
                {Joined setRight(Curr)}
            else
                Joined = Curr
            end
        end

        fun {Lifter Value}
            {New Node init(Value)}
        end

        Tokens = {Lex Line}
    in
        {BuildTree Env Joiner Lifter Tokens Expr}
    end
end

proc {ParseProgram Stream}
    local
        Lines = {String.tokens Stream &\n}
        Size = {List.length Lines}
        SuperCombs = {List.take Lines (Size-1)}
        Call = {List.last Lines}

        Env = {New Store init}
    in
        for S in SuperCombs do
            {ParseSuperComb Env S}
        end

        local Expr = {ParseCall Env Call} in
            {Eval Env Expr}
            {Preorder Expr}
        end
    end
end

%-----------

proc {Test}
    local Testcases = ["square.txt" "diffsquare.txt" "twice.txt" "fourtimes.txt" "noneval.txt" "composition.txt"] in
        for T in Testcases do
            local Content = {List.append "testcases/" T} in
                {Browse {List.append "Executing " T}}
                {ParseProgram {ReadFile Content}}
            end
        end
    end
end

{Test}