////////////////////////////////////////////////RTL/////////////////////////////////////////////

module up_DW_counter( clock,din,load,mode,reset, count);
  input clock;
  input  [3:0] din;
  input load,mode,reset;
  output reg [3:0] count = 0;
  
  always @(posedge clock)
    begin
   if(reset == 1)
        count <= 0;
    else if (load == 1)
        count <= din;
    else if(mode == 1)
        begin
          if (count >= 11)
           count <= 4'b0;
          else 
        count <= count + 1'b1;
        end
  else
    begin
      if(count == 0)
        count <= 4'd11;
      else 
        count <= count - 1'b1;
    end
     // $display("The count is %0d",count);
    end

property  reset_check;
    @(posedge clock) $rose(reset) |-> ##1  count==0;
endproperty

RESET : assert property ( reset_check ) $display("RESET PASS"); else $display("RESET FAILED");


property load_check;
   @(posedge clock) load |=> count == din;
endproperty

LOAD : assert property ( load_check ) $display("LOAD PASS"); else $display("LOAD FAILED");


sequence mode_check_1_seq;
   (~reset) && (mode == 1) && (count >= 11);
endsequence

property mode_check_1;
    @(posedge clock) mode_check_1_seq |=> count == 0;
endproperty 

MODE : assert property ( mode_check_1 ) $display("MODE_CHECK_1 PASS"); else $display("MODE_CHECK_1 FAILED");


sequence mode_check_2_seq;
    (~reset) && (mode == 1) && ( count <= 11 );
endsequence

property mode_check_2;
   @(posedge clock) mode_check_2_seq |=> count == $past(count) + 1'b1;
endproperty

MODE_2 : assert property ( mode_check_1 ) $display("MODE_CHECK_2 PASS"); else $display("MODE_CHECK_2 FAILED");


sequence mode_check_3_seq;
    (~reset) && (mode == 0) && ( count <= 0 );
endsequence


property mode_check_3;
    @(posedge clock) mode_check_3_seq |=> count == 4'd12;
endproperty

MODE_3 : assert property ( mode_check_3 ) $display("MODE_CHECK_3 PASS"); else $display("MODE_CHECK_3 FAILED");


sequence mode_check_4_seq;
    (~reset) && (mode == 0) ;
endsequence


property mode_check_4;
           @(posedge clock) mode_check_4_seq |=> count == $past(count) + 1'b1;
endproperty

MODE_4 : assert property ( mode_check_4 ) $display("MODE_CHECK_4 PASS"); else $display("MODE_CHECK_4 FAILED");



endmodule



/*
module test();
 
   reg clock;
   reg [3:0] din;
   reg load;
   reg mode;
   reg reset;
   wire [3:0] count;
   parameter timee = 5;

  up_DW_counter dut(.clock(clock), .din(din), .load(load), .mode(mode), .reset(reset), .count(count));

    task initiall();
    din = 0;
    load = 0;
    mode = 0;
    reset = 0;
    //count = 0;
 
     endtask


   task reset_1();
      reset = 1;
      #(timee);
      reset = 0;
   endtask

   task mode_1();
     mode = 1;
   endtask


   task mode_0();
     mode = 0;
   endtask

 
   task load_1(input loadd);
      load = 1;
      din = loadd;
       load = 0;
    endtask

  initial begin
    clock = 0;
   forever #(timee) clock = ~ clock; 
    end
 
  initial begin
    initiall();
    reset_1();
    #((timee)/2);
     mode_1();
    #50;
     mode_0();
    #50;
     load_1(4);
    #50;
     reset_1();
    #50;
     #200 $finish;
   end 

initial $monitor($time,"the reset=%0d \t mode = %0d \t load = %0d \t din = %0d \t count = %0d",reset,mode,load,din,count);
endmodule
*/
