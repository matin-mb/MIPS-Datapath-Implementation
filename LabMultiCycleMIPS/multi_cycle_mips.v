`timescale 1ns/100ps
// Matin Mb 400102114 
// MultiCycle Lab

   // LUI is added so we need 4bits:
   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'b1000

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // For MFLO , MFHI , MULT:
   reg [31:0] hi,lo;
   wire [63:0] MULTout;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;
   
   reg [1:0] PCSrc;
   wire [31:0] PCjump = {PC[31:28], IR[25:0], 2'b0};


   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [3:0] aluOp;
   reg [1:0] aluSelB;
   reg SgnExt, aluSelA, IorD;
   reg multStart;
   reg [1:0] RegDst;
   reg [2:0] MemtoReg;
   

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire ready;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt)
         case (PCSrc)
         2'b00: PC <=#0.1 aluResult;
         2'b01: PC <=#0.1 PCjump;
         2'b10: PC <=#0.1 A;         
         endcase

   
      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;

      if(ready) {hi,lo} <= #0.1 MULTout;

   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),       
      .WR( RegDst[1] ? 5'b11111 : ( RegDst[0] ? IR[15:11] : IR[20:16] )), //Regdst[1] for Ja($ra)
      .WD( MemtoReg[2] ? PC : (MemtoReg[1] ? (MemtoReg[0] ? hi : lo) : (MemtoReg[0] ? MDR : aluResult )))

      // Note:
      // RegDst { 10-> $ra / 00-> $rt / 01 -> $rd }
      // Mem2Reg { 1xx -> PC / 011 -> hi / 010 -> lo / 001 -> MDR / 000 -> ALURes}
      

   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase

   

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),
      .X( aluResult ),
      .Z( aluZero )
   );

   multiplier mult(
      .clk( clk ),  
      .multStart( multStart ),
      .mulA( aluA ), 
      .mulB( aluB ), 
      .Product( MULTout ),
      .ready( ready )
    ); 

   // Controller Starts Here

   // Controller State Registers
   reg [5:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26,
      EX_J = 27, EX_J_2 = 28 , EX_JAL_1 = 29, EX_JAL_2 = 30, EX_JR_1 = 31,EX_JR_2 = 32,
      EX_MF = 33, EX_MULTU_1 = 34,EX_MULTU_2 = 35;


   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;
      multStart = 0;

      SgnExt = 'bx; IorD = 'bx; 
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;

      PCSrc = 'bx;

      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;


      

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            PCSrc = 0;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ; 
                     3'b001: nxt_state = EX_JR_1; // jr and jalr
                     3'b010: nxt_state = EX_MF; // mflo/hi
                     3'b011: nxt_state = EX_MULTU_1; 
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,             // xori
               6'b001_111:             // lui
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;  //beq-bne
                  
               6'b000_010:
                  nxt_state = EX_J; //j

               6'b000_011:
                  nxt_state = EX_JAL_1; //jal

                  
                  


            endcase
         end

         EX_ALU_R: begin
            aluSelA = 1; //A
            aluSelB = 2'b00; // B
            MemtoReg = 3'b000; // ALURes
            RegDst = 2'b01; // $rd
            RFwrt = 1;
            case(IR[5:0])
            6'b100000: aluOp = `ADD;
            6'b100010: aluOp = `SUB;
            6'b100001: aluOp = `ADD;
            6'b100011: aluOp = `SUB;
            6'b100100: aluOp = `AND;
            6'b100101: aluOp = `OR;
            6'b100110: aluOp = `XOR;
            6'b100111: aluOp = `NOR;
            6'b101010: aluOp = `SLT;
            6'b101011: aluOp = `SLTU;
         endcase
         PrepareFetch;
         end

         EX_ALU_I: begin
            aluSelA = 1; // A
            aluSelB = 2'b10; //Szout
            MemtoReg = 3'b000; //ALURes
            RegDst = 2'b00; // $rt
            RFwrt = 1; 
            case(IR[31:26]) //funct field 
            6'b001_000: 
               begin 
               SgnExt = 1;
               aluOp = `ADD; 
               end
            6'b001_001:
               begin 
               SgnExt = 1;
               aluOp = `ADD; 
               end
            6'b001_010: 
               begin 
               SgnExt = 1;
               aluOp = `SLT; 
               end
            6'b001_011: 
               begin 
               SgnExt = 0;
               aluOp = `SLTU; 
               end
            6'b001_100:
               begin 
               SgnExt = 0;
               aluOp = `AND; 
               end
            6'b001_101: 
               begin 
               SgnExt = 0;
               aluOp = `OR;
                end
            6'b001_110: 
               begin 
               SgnExt = 0;
               aluOp = `XOR; 
               end
            6'b001_111: 
               begin 
               SgnExt = 1'bx;
               aluOp = `LUI;
               end
         endcase
         PrepareFetch;
         end

         EX_LW_1: begin
            SgnExt = 1;
            aluSelA = 1; //A
            aluSelB = 2'b10; //Szout            
            aluOp = `ADD; 
            setMRE = 1;
            IorD = 1; // MAR = AluRes
            MARwrt = 1;
            nxt_state = EX_LW_2;
         end

         EX_LW_2: 
            nxt_state = EX_LW_3;
         

         EX_LW_3: 
            nxt_state = EX_LW_4;
         

         EX_LW_4: begin
            clrMRE = 1;
            MDRwrt = 1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            MDRwrt=0;
            MemtoReg=3'b001; //MDR
            RFwrt = 1;
            RegDst = 2'b00; // $rt

            PrepareFetch;
         end

         EX_SW_1: begin
            SgnExt = 1;
            aluSelA = 1; // A
            aluSelB = 2'b10; // Szout            
            aluOp = `ADD;
            setMWE = 1;
            IorD = 1;
            MARwrt = 1;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BRA_1: begin
            aluSelA = 1; // A
            aluSelB = 2'b00; // B
            aluOp = `SUB;            
            if(aluZero ^ IR[26]) //beq-bne 
               nxt_state = EX_BRA_2;
            else
               PrepareFetch;
         end

         EX_BRA_2: begin
            SgnExt = 1;
            aluSelA = 0; // PC
            aluSelB = 2'b11;  //Szout << 2          
            aluOp = `ADD;
            MARwrt = 1;
            setMRE = 1;
            PCwrt = 1;                        
            PCSrc = 2'b00; //ALURes
            IorD = 1; // Mar = ALURes
            nxt_state = FETCH1;
         end


         EX_J: begin
            PCSrc = 2'b01; // $PCjump
            PCwrt = 1;            
            nxt_state = EX_J_2;
         end

         EX_J_2: begin
            PrepareFetch;
         end

         EX_JAL_1: begin
            aluSelA = 0; // PC
            aluSelB = 2'b01; // 32'h4
            aluOp = `ADD;
            MemtoReg = 3'b100; // PC
            RegDst = 2'b10; // $ra
            RFwrt = 1;
            PCwrt = 1;
            PCSrc = 2'b01; // PCjump
            nxt_state = EX_JAL_2;
         end

         EX_JAL_2: begin
            PrepareFetch;
         end

         EX_JR_1: begin
            PCwrt = 1;
            PCSrc = 2'b10; // PC_src = [A]

            if((IR[2:0]==3'b001)) //Jump and Link register 
            begin           
               aluSelA = 0; // PC
               aluSelB = 2'b01; // 32'h4
               aluOp = `ADD; 
               RFwrt = 1;                
               MemtoReg = 3'b100;  // Writes PC
               RegDst = 2'b10;  // $ra               
            end
         
               nxt_state = EX_JR_2;
         end

         EX_JR_2: begin
            PrepareFetch;
         end

         EX_MF: begin

            if (IR[1]) //lo
               MemtoReg = 3'b010;               
            if (!IR[1]) //hi
               MemtoReg = 3'b011; 

            RegDst = 2'b01; //[rd]
            RFwrt = 1; 

            PrepareFetch;
         end

         EX_MULTU_1: begin
            multStart = 1;
            aluSelA = 1; // A
            aluSelB = 2'b00; // B           
            nxt_state = EX_MULTU_2;
         end

         EX_MULTU_2: begin            
            if(~ready)    //Waits until MULTout is ready          
                  nxt_state = EX_MULTU_2;
            else
               PrepareFetch;                  
         end

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [3:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `LUI : x = {B[15:0], 16'h0}; // Added from singleCycle ALU
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

//OK


`timescale 1ns/1ns
// Matin Mb 400102114 
// 3.1 Optimized multiplier
module multiplier(
//-----------------------Port directions and deceleration
   input clk,  
   input multStart,
   input [31:0] mulA, 
   input [31:0] mulB, 
   output reg [63:0] Product,
   output ready
    );


//----------------------------------- register deceleration
reg [31:0] Multiplicand ;
//reg [7:0]  Multiplier; // Note that multiplier is placed in product [15:8]
reg [5:0]  counter;

//------------------------------------- wire deceleration
wire [31:0] s;
wire Cout;
wire  [31:0] Mux;
//---------------------------------------------------------

//-------------------------------------- combinational logic
assign Mux = Product[0] ? Multiplicand : 0 ;
assign ready = counter[5];
assign {Cout,s} = Mux + Product[63:32];

//--------------------------------------- sequential Logic
always @ (posedge clk)

   if(multStart) begin
        counter <= 6'h0 ;
		  Product <= 64'h0;
		  Multiplicand <= mulA ;
		  Product[53:32] <= 0;
		  Product[31:0] <= mulB;
		  		  
   end
   else if(! ready) begin
         counter <= counter + 1;
			Product[63] <= Cout;	
			Product[62:32] <= s[31:1];
			Product[31] <= s[0];
			Product[30:0] <= Product[31:1];			
   end   

endmodule