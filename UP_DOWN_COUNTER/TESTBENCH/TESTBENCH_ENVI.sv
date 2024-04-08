
////////////////////////////////////////////////INTERFACE//////////////////////////////////////////


interface counter(input bit clock);  //interface declaration
  logic [3:0] count;
  logic [3:0] din;
  logic mode;
  logic reset;
  logic load;
  
  
  clocking write_D @(posedge clock); //clocking block for WRITE_DRIVER
    default input #1 output #1;
    output din;
    output mode;
    output reset;
    output load;
    endclocking
  
  clocking write_M @(posedge clock);  //clocking block for WRITE_MONITOR
    default input #1 output #1;
    input din;
    input mode;
    input reset;
    input load;
    endclocking
  
  
  clocking read_M @(posedge clock);  //clocking block for READ_MONITOR
    default input #1 output #1;
    input count;
    endclocking
    
  modport MP_WD (clocking write_D);    //modport for for WRITE_DRIVER
    modport MP_WM (clocking write_M);  //modport for for WRITE_MONTOR
      modport MP_RM (clocking read_M); //modport for for READ_MONITOR
  
endinterface
/////////////////////////////////////////////////////////////////////////////////////////////////////////


package pkt;
 int no_of_transaction = 1; 
//`include "counter_duv.sv"      
endpackage


import pkt::*;

///////////////////////////////////////////////////TRANSACTION//////////////////////////////////////////

class Transaction;						//Transactions dairy
  rand bit [3:0] din;
    rand bit mode;
    rand bit reset;
    rand bit load;
  
  logic [3:0] count;                   // output count
  
  constraint C1 {reset dist{ 0 := 10 , 1 := 1};} //Reset is 0 for 10 and 1 for 1
  constraint C2 {load dist{ 0 := 4 , 1 := 1};}   //load is 0 for 4 and 1 for 1
  constraint C3 {mode dist{ 0 := 10 , 1 := 10};} //mode is 0 for 10 and 1 for 10
  constraint C4 {din inside {[1:10]};}           //din is selected within 1 to 10
 
  function void display(input string str);
    $display("--------------------------START---------------------------------------");
    $display("The Display getting from %0s",str);
    $display("The value of reset = %0d \t load = %0d \t mode = %0d \t din = %0d",reset,load,mode,din);  
    $display("---------------------------END----------------------------------------");
  endfunction
  
 /* function Transaction copy();						//DEEP-COPY if in case needed
     copy.din =   din;
     copy.mode =  mode;
     copy.reset = reset;
     copy.load =  load;
     //copy.count = count;
  endfunction   */
endclass
    
////////////////////////////////////////////////////GENERATOR//////////////////////////////////////////////
   //import pkt::*;
class Generator;
  
  Transaction trans, trans_copy;						
  
  mailbox #(Transaction) gen2driv;
  
  function new(mailbox #(Transaction) gen2driv); //from ENVI we create object for GENERATOR with the object creation we give a mailbox as overraiding constructor 
    this.gen2driv = gen2driv;
    trans = new();                 //creating a constructor outside loop to avoid same rendom numbers as we just give deep copied trans to mailbox 
  endfunction
  
  task run_gen();
    
    fork    
      for(int i = 0 ; i < no_of_transaction ; i ++)
      begin
        assert(trans.randomize()) else $display("RANDOMIZE FAILED");
        trans_copy = new trans;
        gen2driv.put(trans_copy);                                    //deep_copy data is put into mailbx
        $display("[GEN]: DATA SENT TO DRIVER");
        trans.display(" Generator");                                           
      end     
    join_none
    
    endtask
  
endclass

/////////////////////////////////////////////////WRITE-DRIVER//////////////////////////////////////////////
    
class Driver;
   virtual counter.MP_WD write;

   mailbox #(Transaction) gen2driv;
  
   Transaction data;
   
  event go;
  
  function new(virtual counter.MP_WD write, mailbox #(Transaction) gen2driv);   //getting write_driver interface and generator2driver from envi
    this.gen2driv = gen2driv;
    this.write = write;
  endfunction
  
  virtual task run_driv();                   ///bee ready when we call u in envi
fork
    forever begin
      gen2driv.get(data);                    ///getting the data from mailbox
      drive();
      data.display("Write-Driver");
    end
join_none
 endtask
      
  virtual  task drive();
    begin
      $display("[WDRIV] : Driving  started (WRITE) ");
      @(write.write_D);
       write.write_D.din <= data.din;
         write.write_D.reset <= data.reset;
       write.write_D.load <= data.load;           
       write.write_D.mode <= data.mode;
      $display("[WDRIV] : Driving  ended (WRITE)");
    end
      endtask
   
endclass : Driver
        
///////////////////////////////////////////////WRITE-MONITOR////////////////////////////////////////////////
        
class Write_monitor;
  
  virtual counter.MP_WM write_m;
  
  Driver drv;
  Transaction data_copy;
  Transaction data_copy_2;                            //just to keep a copy safe
  
  mailbox #(Transaction) write_M2RM;
  
  function new (virtual counter.MP_WM write_m ,  mailbox #(Transaction) write_M2RM ); //write_monitor interface and monitor2refmodule
     this.write_M2RM =  write_M2RM ;
    this.write_m = write_m;
    data_copy = new();          
  endfunction
  
  virtual task monitor();
  begin
    @(write_m.write_M);
    begin
      $display("[WDMON] : Monitoring  started (WRITE) ");
    data_copy.din  =  write_m.write_M.din;
    data_copy.reset  =  write_m.write_M.reset;
    data_copy.load  =  write_m.write_M.load;
    data_copy.mode  =  write_m.write_M.mode;
      $display("[WDMON] : Monitoring  ended (WRITE)");
    end
  end
    
  endtask
  
  virtual task run_writeMoni(); 
  fork  
    forever begin
      monitor();
     data_copy.display("Write_MONITER");
      //$display("The din = %0d \t mode = %0d \t reset = %0d \t load = %0d",data_copy.din,data_copy.mode,data_copy.reset,data_copy.load);
      data_copy_2 = new data_copy;         
      write_M2RM.put(data_copy_2);     ///sacrifice the data_copy_2 (the content of interface is given to mailbox(refModel))
    end
  join_none
  endtask
  
endclass : Write_monitor
        
////////////////////////////////////////////////READ-MONITOR/////////////////////////////////////////        
        
        
 class Read_monitor;
   
   virtual counter.MP_RM read_m;
   
   mailbox #(Transaction) read_M2SC;
   mailbox #(Transaction) read_M2RM;
   
   Transaction data_recive;
   Transaction data_recive_copy;
   Transaction data_checker;

    int q[$];                          ///sacrifice sheep
   
   function new (virtual counter.MP_RM read_m,  mailbox #(Transaction) read_M2SC ); //read_monitor and readmoni2scorebord
     this.read_M2SC =  read_M2SC ;
    this.read_m = read_m;
    data_recive = new();
  endfunction
   
   virtual task read_from_duv();  
     begin
       @(read_m.read_M);             ///wait for a cycle
       begin
         $display("[RDMON] : Monitoring  started (READ) ");
     data_recive.count = read_m.read_M.count;  ///what ever count value u got from interface just store it in local storage
     checker_1(data_recive);
         $display("++++++++DUT-COUNTER+++++++");
         $display("The DUT-COUNTER is %0d",read_m.read_M.count);
         $display("++++++++END-COUNTER+++++++");
    // $display("The counter value is %0d",);
         $display("[RDMON] : Monitoring  ended (READ) ");
       end
     end
   endtask
   
   virtual task run_readMoni(); ///main
      fork
        forever begin
       read_from_duv();  
          data_recive.display("Read Monitor");
       data_recive_copy = new data_recive;   ///sacrifice sheep
       read_M2SC.put(data_recive_copy);  ///put the datafile(local storage) to mailbox(scoreboard)   
      q.push_back(data_recive.count);
          //$display("The COUNTER value recived by READ-MON are %0p",q);
        end
      join_none
   endtask   
       
       task checker_1(Transaction data_checker);
         if(data_checker.count != 0 || data_checker.count >= 1) $display("[CHECK_1]: 1.The counter op is %0d",data_checker.count);
         else $display("[CHECK_1]: 2. The counter op is %0d",data_checker.count);
         endtask
    
 endclass :  Read_monitor
        
//////////////////////////////////////////////////REFRENCE-MODEL///////////////////////////////////////////        
        
class Refrence_model;
  Transaction data_wm;
  Transaction data_wm_copy;
  
  mailbox #(Transaction) write_M2RM;   //from write monitor
  mailbox #(Transaction) ref_M2SC;   //from refrence model to scoreboard
  
  logic [3:0] count_ref = 0;
  
  function new( mailbox #(Transaction) write_M2RM,
               mailbox #(Transaction) ref_M2SC);
    this.write_M2RM = write_M2RM;
    this.ref_M2SC = ref_M2SC;
  endfunction
  
 
  task process(Transaction data);       ///just same counter logic
    if(data.reset)
        count_ref <= 4'b0000;
    else if (data.load)
        count_ref <= data.din;
    else if(data.mode == 1)
        begin
          if (count_ref >= 11)
           count_ref <= 4'b0;
          else 
        count_ref <= count_ref + 1'b1;
    end
    else if (data.mode == 0)
    begin
      if(count_ref == 0)
        count_ref <= 4'd11;
      else 
        count_ref <= count_ref - 1'b1;
    end
    
  endtask
  
  virtual task run_refMode();
    fork    
        forever
          begin
                  write_M2RM.get(data_wm);                //get the data from write monitor(mailbox)
                  data_wm_copy = new data_wm;             //copy it down (shallow)
                  process(data_wm_copy);                  //ubdate  count_ref through calling process
                  data_wm_copy.count = count_ref;         //copy the count_ref to local copy count
                  ref_M2SC.put(data_wm_copy);             //put the copied data to mailbox(scoreboard)
                  data_wm.display("Refrence Model");
            $display("+++++++INNER-COUNTER++++++");
            $display("The COUNT_REF is %0d",data_wm_copy.count);
            $display("++++++++END-COUNTER+++++++");
          end   
    join_none
  endtask
 
endclass
        
///////////////////////////////////////////////SCOREBOARD///////////////////////////////////////////////        
 //import pkt::*; 
 class Scoreboard;
   event done;
   
   Transaction data_RMOD;
   Transaction data_READM;
   Transaction cover_data;

 int  queue_1[$];
  int queue_2[$];
  // Transaction data_verify;
   
   static int data_verified, data_recived_RMOD, data_recived_REMONI, data_correct, data_incorrect;  //just checking
   
   mailbox #(Transaction) read_RM2SC;      //read_monitor
   mailbox #(Transaction) read_REM2SC;     //ref_model
   
     covergroup cg;

     option.per_instance = 1;
     option.comment = "The Coverage on Reset/load/mode";
     option.cross_num_print_missing = 100;
        
      RESET : coverpoint cover_data.reset{
                         bins XERO = {0};
                         bins OONE = {1};
                                }
 
      LOAD : coverpoint cover_data.load {
                         bins XERO = {0};
                         bins OONE = {1};
                              }
      MODE : coverpoint cover_data.mode {
                         bins XERO = {0};
                         bins OONE = {1};
                              }
      DATA_IN : coverpoint cover_data.din {
                         bins FIRST = {[0:6]};
                         bins SECOND = {[7:12]};
                                }

     RESETxLOADxMODE : cross RESET,LOAD,MODE;

   endgroup

   function new( mailbox #(Transaction) read_RM2SC,
                mailbox #(Transaction) read_REM2SC);
    this.read_RM2SC = read_RM2SC;
    this.read_REM2SC = read_REM2SC;
         cg = new();
          endfunction
   
   
  virtual task run_score();
     fork
     forever
         begin
           read_RM2SC.get(data_RMOD);       //get the data from read monitor and store it in local data (x)
           data_recived_RMOD++;               //increment recived
           read_REM2SC.get(data_READM);      //get the data from refrence_model and store it in local data (y)
           data_recived_REMONI++; 
            cover_data = new data_RMOD;
           cg.sample();
           compare(data_READM);              //call compare
           pushing_into_it(data_READM);
         end
       join_none    
   endtask

      



   virtual task compare(Transaction data_verify);     ///the y is begin compared with x value
     begin
       if( data_RMOD.count == data_verify.count)  // y.count == x.count
       begin
         data_correct++;                         //if yes data_correct incremented
         $display("--------------------------------RESULT---------------------------------------");
         $display("[SCR] : DATA VALID COUNT = %0d",data_correct);
         $display("-------------------------------END-RESULT------------------------------------");
       end
     else begin
       data_incorrect++;  
       $display("---------------------------------RESULT-----------------------------------------");
       $display("[SCR] : DATA INVALID COUNT = %0d",data_incorrect);
       $display("-------------------------------END-RESULT---------------------------------------");
     end
     end

     data_verified++;
     if(data_verified >= no_of_transaction  )
           -> done;        //when no of transcation reached data verified trigger done
   endtask
   
   function void report();
     $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
     $display("====================SCOREBOARD=====================");
     $display("Data recived by Refrence Model are : %0d",data_recived_REMONI);
     $display("Data recived by Read Monitor are : %0d",data_recived_RMOD);
     $display("Data Correct are : %0d", data_correct);
     $display("Data Incorrect are : %0d", data_incorrect);
     $display("Data Verified are : %0d",data_verified);  
     $display("Coverage Report is ",cg.get_coverage);
     $display("The Values from Read_Monitor is %0p",queue_1);
     $display("The Values from Refrence_Model is %0p",queue_2);
     $display("==================SCOREBOARD-ENDS=================="); 
     $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");         
   endfunction 
              
  function void pushing_into_it(Transaction data_READM_1);

     queue_1.push_front(data_READM_1.count);
     queue_2.push_front(data_RMOD.count);
     
  endfunction
 
 endclass
     
              
////////////////////////////////////////////////ENVIRONMENT//////////////////////////////////////////////              
              
class Enviornment;
  
   virtual counter.MP_WD write;             
   virtual counter.MP_WM write_m;
   virtual counter.MP_RM read_m;
  
  mailbox #(Transaction) gen2driv = new();                //creating constructor to mailbox
  mailbox #(Transaction) write2ref = new();
  mailbox #(Transaction) readm2scoreb = new();
  mailbox #(Transaction) ref2scoreb = new();
  
  Generator gen ;                                         //creating handle for tb components
  Driver  driv;
  Write_monitor w_moni ;
  Read_monitor r_moni;
  Refrence_model ref_mode ;
  Scoreboard  scrb;
  
  function new ( virtual counter.MP_WD write,             //getting interface from testcase
   virtual counter.MP_WM write_m,
   virtual counter.MP_RM read_m);
    this.write = write;
    this.write_m =  write_m;
    this.read_m = read_m;
  endfunction
  
  virtual task build();                                   //creating constructori to all tb component and passing the required interface handel
  
    gen = new(gen2driv);                                  // and mailbox    
     driv = new(write,gen2driv);
     w_moni = new(write_m,write2ref);
     r_moni = new(read_m,readm2scoreb); 
     ref_mode = new(write2ref,ref2scoreb);
     scrb = new(ref2scoreb,readm2scoreb);
 
   endtask
  
  task start();                                          //starting all at once

    gen.run_gen();
    driv.run_driv();
    w_moni.run_writeMoni();
    r_moni.run_readMoni();
    ref_mode.run_refMode();
    scrb.run_score();

  endtask
  
  task stop();                //stop when we get trigger
    wait(scrb.done.triggered);  
  endtask
  
 virtual task run_envi();
   start();
   $display("[ENV] OPERATION STARTED");
    stop();
   $display("[ENV] OPERATION ENDED");

    scrb.report();
   $display("[ENV] REPORT GENERATED");
   $finish;
  endtask
  
endclass
              
////////////////////////////////////////////////////TESTCASE///////////////////////////////////////////////////////
              
class testcase_1;
  
   virtual counter.MP_WD write;                     // virtual interface
   virtual counter.MP_WM write_m;
   virtual counter.MP_RM read_m;
  
  Enviornment envi;      
    int  no_of_transaction = 100;
  
  function new ( virtual counter.MP_WD write,
   virtual counter.MP_WM write_m,
   virtual counter.MP_RM read_m);
    this.write = write;
    this.write_m =  write_m;
    this.read_m = read_m;
    
    envi = new(write,write_m,read_m);
    
  endfunction
  
  task build;
    envi.build();
  endtask
  
  task run;
    envi.run_envi();
   endtask
    
endclass
              
              
/////////////////////////////////////////////////TOPMODULE/////////////////////////////////////////////////////
 //import pkt::* ;
//`include "counter_duv.sv"     
module TopModule();
 //  import pkt::* ;

  reg clock;
  
  
  counter count(clock);       //interface
  
  testcase_1 test_1;          //testcase
  
  parameter cycle = 10;
  
  up_DW_counter DUV (.clock(clock), .din(count.din), .load(count.load), .mode(count.mode), .reset(count.reset), .count(count.count));
  
  initial begin
    no_of_transaction = 10;
    test_1 = new(count,count,count);
    test_1.build;
    test_1.run;
   // $finish;
      end
  
  initial begin
    clock = 1'b0;
    forever #(cycle/2) clock = ~clock;
  end
  
  //initial begin
   // $dumplfile("dump.vcd");
  //  $dumpvars;
 // end
  
endmodule

//////////////////////////////////////////////////THE-END//////////////////////////////////////////////////            
        














