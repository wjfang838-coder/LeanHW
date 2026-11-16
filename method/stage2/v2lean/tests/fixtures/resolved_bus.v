module resolved_bus(input a,b,ea,eb,inout bus,output observed);
  assign bus = ea ? a : 1'bz;
  assign bus = eb ? b : 1'bz;
  assign observed = bus;
endmodule
